From Minuska Require Import
    prelude
    spec
    default_static_model
    builtin.int_signature
    builtin.int_model
    pi.trivial
.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation.


(* Existing Instance int_model. *)

#[local]
Instance Σ : StaticModel := @default_model int_signature (int_model _ _ _) MyProgramInfo.

#[local]
Instance show_builtin : Show builtin_value := {|
    show := fun x => match x with inl b => show b | inr z => show z end
|}.

Definition genBuiltin : G builtin_value :=
    oneOf_ (returnGen (inl true)) [(returnGen (inl true)); (returnGen (inl false)); (returnGen (inr 1%Z));(returnGen (inr 2%Z))]
.

Sample genBuiltin.
(* Print TermOver'. *)
Fixpoint show_to (t : TermOver builtin_value) : string  :=
    match t with
    | t_over b => show b
    | t_term s l => show s +:+ "(" +:+ (concat "," (show_to <$> l ))  +:+ ")"
    end
.

#[local]
Instance showTerm : Show (TermOver builtin_value) := {|
    show := show_to ;
|}.

Fixpoint genTermSized (sz : nat) : G (TermOver builtin_value) :=
  match sz with
    | O => bindGen genBuiltin (fun x => returnGen (t_over x))
    | S sz' =>
        freq [ (1, bindGen genBuiltin (fun x => returnGen (t_over x))) ;
                (sz, bindGen (oneOf_ (returnGen "") [(returnGen "s");(returnGen "t");(returnGen "a");(returnGen "b");(returnGen "c")])
                (fun s => bindGen (listOf (genTermSized sz')) (fun l => returnGen (t_term s l))))
             ]
  end.


(* Check returnGen. *)
Sample (genTermSized 1).


