From Minuska Require Import
    prelude
    spec
    ocaml_interface
.


Inductive Emptyset : Set := .

#[export]
Instance emptyset_eqdec : EqDecision Emptyset.
Proof.
    intros x y.
    destruct x, y.
Defined.

#[export]
Program Instance emptyset_fin : Finite Emptyset := {|
    enum := [];
|}.
Next Obligation.
    constructor.
Qed.
Next Obligation.
    destruct x.
Qed.
Fail Next Obligation.


Section sec.

    Context
        {TermSymbol : Set}
        {TermSymbols : Symbols TermSymbol}
    .

    #[local]
    Program Instance mysignature : Signature := {|
        FunSymbol
            := Emptyset ;
        PredSymbol
            := Emptyset ;
    |}.
    Fail Next Obligation.

    Program Definition βover
        : ModelOver mysignature MyUnit Emptyset := {|
        builtin_function_interp
            := fun _ _ _ => None ;
        builtin_predicate_interp
            := fun _ _ _ => None ;
    |}.
    Fail Next Obligation.

    #[local]
    Instance β
        : @Model _ _ mysignature MyUnit := {|
        BasicValue
            := Emptyset ;
        builtin_model_over := βover ;
    |}.

End sec.

Definition bindings (Q : Type) : string -> SymbolInfo Emptyset void Emptyset void Q void
:=
    fun s => si_none _ _ _ _ _ _
.