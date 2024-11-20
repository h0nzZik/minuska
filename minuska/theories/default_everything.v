From Minuska Require Export
    prelude
    spec
    basic_properties
    string_variables
    default_static_model
    frontend
    properties
    naive_interpreter
    interpreter_results
.

Require Extraction.
Extraction Language OCaml.
Require Export
  Coq.extraction.Extraction
  Coq.extraction.ExtrOcamlBasic(*
  Coq.extraction.ExtrOcamlChar
  Coq.extraction.ExtrOcamlString*)
  Coq.extraction.ExtrOcamlZBigInt
  Coq.extraction.ExtrOcamlNatBigInt
.
From Coq Require Import String Bool Arith ZArith List.

Require Minuska.BuiltinValue Minuska.builtins.

Variant Act := default_act | invisible_act.


#[export]
Instance Act_eqDec : EqDecision Act.
Proof.
    ltac1:(solve_decision).
Defined.

Definition myBuiltinType : Type := @BuiltinValue.BuiltinValue0 string.
Module dmyBuiltin := builtins.default_builtin.
Export dmyBuiltin.
Definition myBuiltin := dmyBuiltin.β.

#[export]
Instance DSM : StaticModel :=
    default_model (myBuiltin)
.

Definition GT := @TermOver' string myBuiltinType.

Definition StepT := NondetValue -> GT -> option GT.

Definition gt_over (b : myBuiltinType) : GT := @t_over string myBuiltinType b.
Definition gt_term (s : string) (l : list GT) : GT := @t_term string myBuiltinType s l.
(*
Definition gt_over b := term_over b.
*)

Definition basic_rule
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (cond : Expression2) : Declaration
:=
    (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act l r [(mkSideCondition2 _ (e_fun builtins.default_builtin.b_true []) cond)] default_act)))
.


Definition BoV_to_Expr2
    {Σ : StaticModel}
    (bov : BuiltinOrVar)
    : Expression2
:=
    match bov with
    | bov_builtin b => (e_ground (t_over b))
    | bov_variable x => e_variable x
    end
.

Definition framed_rule
    (frame : (variable*(TermOver BuiltinOrVar)))
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (cond : Expression2) : Declaration
:=
    (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act
        (TermOverBoV_subst frame.2 frame.1 l)
        (TermOverBoV_subst_expr2 frame.2 frame.1 r)
        [(mkSideCondition2 _ (e_fun builtins.default_builtin.b_true []) cond)] default_act)))
.

Definition global_naive_interpreter := @naive_interpreter DSM Act.
Definition global_naive_interpreter_sound := @naive_interpreter_sound DSM Act.
Definition builtins_binding := Minuska.builtins.builtins_binding.