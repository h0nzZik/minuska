
From Minuska Require Import
    prelude
    spec
    specb
    default_static_model
    builtin.int_signature
    builtin.int_model
    pi.trivial
.
About stdpp.strings.String.
Locate String.
From QuickChick Require Export QuickChick.
Export QcDefaultNotation.

#[export]
Instance Σ : StaticModel := @default_model int_signature (int_model _ _ _) MyProgramInfo.

#[export]
Instance show_builtin : Show builtin_value := {|
    show := fun x => match x with inl b => show b | inr z => show z end
|}.

Definition genBuiltin : G builtin_value :=
    oneOf_ (returnGen (inl true)) [(returnGen (inl true)); (returnGen (inl false)); (returnGen (inr 1%Z));(returnGen (inr 2%Z))]
.

#[export]
Instance show_symbol : Show symbol := {|
    show := fun x => x;
|}.

Fixpoint show_to {T : Type} {_ST : Show T} (t : TermOver T) : string  :=
    match t with
    | t_over b => show b
    | t_term s l => show s +:+ "[" +:+ (concat "," (show_to <$> l ))  +:+ "]"
    end
.

#[export]
Instance showTerm {T : Type} {_ST : Show T} : Show (TermOver T) := {|
    show := show_to ;
|}.

#[export]
Instance showBuiltinOrVar {T : Type} {_ST : Show T} : Show (BuiltinOrVar) := {|
    show := fun bov => match bov with bov_builtin b => show b | bov_variable x => show x end;
|}.

Definition genVariable : G variable :=
    oneOf [ret "x"; ret "y"; ret "z"; ret "xx"; ret "yy"; ret "zz"]
.

Definition genSymbol : G symbol :=
    (oneOf [(returnGen "s");(returnGen "t");(returnGen "a");(returnGen "b");(returnGen "c")])
.

(* Print IntFunSymbol. *)
(* Compute builtin_function_symbol. *)

Definition genFunction : G builtin_function_symbol :=
    elems [int_plus; int_minus; int_uminus; int_zero; int_one; int_eq; int_le; int_lt]
.

Fixpoint genTermSized' {T : Type} (sz : nat) (g : nat -> G T) : G (TermOver T) :=
  match sz with
    | O => bindGen (g sz) (fun x => returnGen (t_over x))
    | S sz' =>
        freq [ (1, bindGen (g sz) (fun x => returnGen (t_over x))) ;
                (sz, bindGen genSymbol
                (fun s => bindGen (listOf (genTermSized' sz' g)) (fun l => returnGen (t_term s l))))
             ]
end.

Definition genTermSized sz := genTermSized' sz (fun _ => genBuiltin).

Definition genBuiltinOrVar := oneOf [bindGen genBuiltin (fun x => ret (bov_builtin x)); bindGen genVariable (fun x => ret (bov_variable x))].


Definition genPatternSized sz := genTermSized' sz (fun _ => 
    genBuiltinOrVar
).
(* Sample (genPatternSized 3). *)
(* Print Expression2. *)

#[export]
Instance showFun : Show builtin_function_symbol := {|
    show := fun f => match (f : builtin_function_symbol) with
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


Fixpoint show_e (e : Expression2) : string  :=
    match e with
    | e_ground g => show g
    | e_variable x => show x
    | e_fun f l => show f +:+ "(" +:+ (concat "," (show_e <$> l ))  +:+ ")"
    | e_query q l => show q +:+ "(" +:+ (concat "," (show_e <$> l ))  +:+ ")"
    end
.

#[export]
Instance showExpr : Show (Expression2) := {|
    show := show_e ;
|}.


Fixpoint genExprSized (sz : nat) : G (Expression2) :=
  match sz with
    | O => oneOf [(bindGen genVariable (fun x => returnGen (e_variable x))); bindGen (genTermSized sz) (fun x => returnGen (e_ground x))]
    | S sz' =>
        freq [
            (1,
                oneOf [(bindGen genVariable (fun x => returnGen (e_variable x))); bindGen (genTermSized sz) (fun x => returnGen (e_ground x))]
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

Definition genValuationSized (sz : nat) : G (gmap variable (TermOver builtin_value)) :=
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


Definition showSubP_ (s : gmap variable (TermOver BuiltinOrVar)) : string :=
        let l := map_to_list s in
        show (l)
.
(* About map_to_list. *)
#[export]
Instance showSubP : Show (gmap variable (TermOver BuiltinOrVar)) := {|
    show := showSubP_
|}.
