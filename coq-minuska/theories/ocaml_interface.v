From Minuska Require Import
    prelude
    spec
.

Variant SymbolInfo (P HP F A Q M : Type)
    :=
| si_none
| si_predicate (p : P)
| si_hidden_predicate (hp : HP)
| si_function (f : F)
| si_attribute (a : A)
| si_query (q : Q)
| si_method (m : M)
.

Definition combine_TermSymbol_classifiers
    {P HP F A Q M : Type}
    (from_pi from_value_algebra from_hidden_algebra : string -> SymbolInfo P HP F A Q M)
    :
    (string -> SymbolInfo P HP F A Q M)
:=
    fun s =>
        match (from_pi s) with
        | si_none _ _ _ _ _ _ =>
            match (from_value_algebra s) with
            | si_none _ _ _ _ _ _ =>
                (from_hidden_algebra s)
            | _ => (from_value_algebra s)
            end
        | _ => (from_pi s)
        end
.

Definition si2qfa
    {Σ : BackgroundModel}
    (si : SymbolInfo PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol)
    :
    option (QuerySymbol+FunSymbol+AttrSymbol)
:=
    match si with
    | si_query _ _ _ _ _ _ q => Some (inl (inl q))
    | si_attribute _ _ _ _ _ _ a => Some (inr a)
    | si_function _ _ _ _ _ _ f => Some (inl (inr f))
    | si_hidden_predicate _ _ _ _ _ _ _ => None
    | si_predicate _ _ _ _ _ _ _ => None
    | si_method _ _ _ _ _ _ _ => None
    | si_none _ _ _ _ _ _ => None
    (* | _ => None *)
    end
.

Definition si2m
    {Σ : BackgroundModel}
    (si : SymbolInfo PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol)
    :
    option (MethSymbol)
:=
    match si with
    | si_query _ _ _ _ _ _ q => None
    | si_attribute _ _ _ _ _ _ a => None
    | si_function _ _ _ _ _ _ f => None
    | si_hidden_predicate _ _ _ _ _ _ _ => None
    | si_predicate _ _ _ _ _ _ _ => None
    | si_method _ _ _ _ _ _ m => Some m
    | si_none _ _ _ _ _ _ => None
    end
.

Definition si2p
    {Σ : BackgroundModel}
    (si : SymbolInfo PredSymbol HPredSymbol FunSymbol AttrSymbol QuerySymbol MethSymbol)
    :
    option (PredSymbol+HPredSymbol)
:=
    match si with
    | si_query _ _ _ _ _ _ q => None
    | si_attribute _ _ _ _ _ _ a => None
    | si_function _ _ _ _ _ _ f => None
    | si_hidden_predicate _ _ _ _ _ _ p => Some (inr p)
    | si_predicate _ _ _ _ _ _ p => Some (inl p)
    | si_method _ _ _ _ _ _ m => None
    | si_none _ _ _ _ _ _ => None
    end
.
