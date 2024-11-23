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

#[export]
Instance DSM {β : Builtin MyUnit} : StaticModel :=
    default_model β
.

Definition GT {β : Builtin MyUnit} := @TermOver' string (builtin_value).

Definition StepT {β : Builtin MyUnit} := NondetValue -> GT -> option GT.
Definition StepT_ext {β : Builtin MyUnit} := NondetValue -> GT -> option (GT*nat).

Definition gt_over {β : Builtin MyUnit} (b : builtin_value) : GT := @t_over string builtin_value b.
Definition gt_term {β : Builtin MyUnit} (s : string) (l : list GT) : GT := @t_term string builtin_value s l.

Definition basic_rule
    {β : Builtin MyUnit}
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (conds : list SideCondition2) : Declaration
:=
    (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act l r conds default_act)))
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
    {β : Builtin MyUnit}
    (frame : (variable*(TermOver BuiltinOrVar)))
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (conds : list SideCondition2) : Declaration
:=
    (decl_rule (@mkRuleDeclaration DSM Act name (@mkRewritingRule2 DSM Act
        (TermOverBoV_subst frame.2 frame.1 l)
        (TermOverBoV_subst_expr2 frame.2 frame.1 r)
        [] default_act)))
.

Definition global_naive_interpreter {β : Builtin MyUnit} := @naive_interpreter DSM Act.
Definition global_naive_interpreter_ext {β : Builtin MyUnit} := @naive_interpreter_ext DSM Act.
Definition global_naive_interpreter_sound {β : Builtin MyUnit} := @naive_interpreter_sound DSM Act.
(* Definition builtins_binding {β : Builtin MyUnit} := Minuska.builtins.builtins_binding. *)