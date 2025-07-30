
From Minuska Require Import
    prelude
    spec
    specb
    default_static_model
    builtin.int_signature
    builtin.int_model
    pi.trivial
    hidden.hidden_unit
.
About stdpp.strings.String.
Locate String.
From QuickChick Require Export QuickChick.
Export QcDefaultNotation.

#[export]
Instance Σ : BackgroundModel
:=
    @default_model
        int_signature
        (unit_hidden_signature int_signature)
        (int_model _ _ _)
        (unit_hidden_model _ _ _)
        MyProgramInfo
.

#[export]
Instance show_builtin : Show BasicValue := {|
    show := fun x => match x with inl b => show b | inr z => show z end
|}.

Definition genBuiltin : G BasicValue :=
    oneOf_ (returnGen (inl true)) [(returnGen (inl true)); (returnGen (inl false)); (returnGen (inr 1%Z));(returnGen (inr 2%Z))]
.

#[export]
Instance show_TermSymbol : Show TermSymbol := {|
    show := fun x => x;
|}.

Fixpoint show_to {T : Type} {_ST : Show T} (t : @TermOver' TermSymbol T) : string  :=
    match t with
    | t_over b => show b
    | t_term s l => show s +:+ "[" +:+ (concat "," (show_to <$> l ))  +:+ "]"
    end
.

#[export]
Instance showTerm {T : Type} {_ST : Show T} : Show (@TermOver' TermSymbol T) := {|
    show := show_to ;
|}.

#[export]
Instance showBuiltinOrVar {T : Type} {_ST : Show T} : Show (BuiltinOrVar) := {|
    show := fun bov => match bov with bov_builtin b => show b | bov_Variabl x => show x end;
|}.

Definition genVariable : G Variabl :=
    oneOf [ret "x"; ret "y"; ret "z"; ret "xx"; ret "yy"; ret "zz"]
.

Definition genSymbol : G TermSymbol :=
    (oneOf [(returnGen "s");(returnGen "t");(returnGen "a");(returnGen "b");(returnGen "c")])
.

(* Print IntFunSymbol. *)
(* Compute FunSymbol. *)

Definition genFunction : G FunSymbol :=
    elems [int_plus; int_minus; int_uminus; int_zero; int_one; int_eq; int_le; int_lt]
.

Fixpoint genTermSized' {T : Type} (sz : nat) (g : nat -> G T) : G (@TermOver' TermSymbol T) :=
  match sz with
    | O => bindGen (g sz) (fun x => returnGen (t_over x))
    | S sz' =>
        freq [ (1, bindGen (g sz) (fun x => returnGen (t_over x))) ;
                (sz, bindGen genSymbol
                (fun s => bindGen (listOf (genTermSized' sz' g)) (fun l => returnGen (t_term s l))))
             ]
end.

Definition genTermSized sz := genTermSized' sz (fun _ => genBuiltin).

Definition genBuiltinOrVar := oneOf [bindGen genBuiltin (fun x => ret (bov_builtin x)); bindGen genVariable (fun x => ret (bov_Variabl x))].


Definition genPatternSized sz := genTermSized' sz (fun _ => 
    genBuiltinOrVar
).
(* Sample (genPatternSized 3). *)
(* Print Expression2. *)

#[export]
Instance showFun : Show FunSymbol := {|
    show := fun f => match (f : FunSymbol) with
    | int_plus => "plus"
    | int_minus => "minus"
    | int_uminus => "uminus"
    | int_zero => "zero"
    | int_one => "one"
    | int_eq => "eq"
    | int_le => "le"
    | int_lt => "lt"
    end ;
|}.

#[export]
Instance showQery : Show QuerySymbol := {|
    show := fun q => match (q : QuerySymbol) with
    | qs_program => "qs_program"
    end ;
|}.

#[export]
Instance showAttribute : Show AttrSymbol := {|
    show := fun a => "some-attribute-TermSymbol" ; 
|}.


Fixpoint show_e (e : Expression2) : string  :=
    match e with
    | e_ground g => show g
    | e_Variabl x => show x
    | e_fun f l => show f +:+ "(" +:+ (concat "," (show_e <$> l ))  +:+ ")"
    | e_query q l => show q +:+ "(" +:+ (concat "," (show_e <$> l ))  +:+ ")"
    | e_attr a l => show a +:+ "(" +:+ (concat "," (show_e <$> l ))  +:+ ")"
    end
.

#[export]
Instance showExpr : Show (Expression2) := {|
    show := show_e ;
|}.


Fixpoint genExprSized (sz : nat) : G (Expression2) :=
  match sz with
    | O => oneOf [(bindGen genVariable (fun x => returnGen (e_Variabl x))); bindGen (genTermSized sz) (fun x => returnGen (e_ground x))]
    | S sz' =>
        freq [
            (1,
                oneOf [(bindGen genVariable (fun x => returnGen (e_Variabl x))); bindGen (genTermSized sz) (fun x => returnGen (e_ground x))]
            );
            (sz, 
                bindGen (listOf (genExprSized sz')) (fun l =>
                    bindGen (genFunction) (fun f =>
                        ret (e_fun f l)
                    )
                )
            )
        ]
  end.


Definition genTermOverExprSized sz := genTermSized' sz genExprSized.

Definition genValuationSized (sz : nat) : G (gmap Variabl (@TermOver' TermSymbol BasicValue)) :=
    bindGen (
        listOf (
            bindGen genVariable (fun x =>
                bindGen (genTermSized sz) (fun g =>
                    returnGen (x, g)
                )
            )
        )
    ) (fun l => returnGen (list_to_map l))
.


Definition showVal_ (ρ : Valuation2) : string :=
        let l := map_to_list ρ in
        show (l)
.
(* About map_to_list. *)
#[export]
Instance showVal : Show Valuation2 := {|
    show := showVal_
|}.


Definition showSubP_ (s : gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)) : string :=
        let l := map_to_list s in
        show (l)
.
(* About map_to_list. *)
#[export]
Instance showSubP : Show (gmap Variabl (@TermOver' TermSymbol BuiltinOrVar)) := {|
    show := showSubP_
|}.
