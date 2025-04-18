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
  Coq.extraction.ExtrOcamlNativeString
  Coq.extraction.ExtrOcamlZBigInt
  Coq.extraction.ExtrOcamlNatBigInt
.

(* Adapted from [Coq.extraction.ExtrOcamlNativeString], using [Stdlib.String] instead of [String]*)
Extract Inductive string => "string"
[
"
  """"
"
"
  (fun (c, s) -> Stdlib.String.make 1 c ^ s)
"
]
"
 (fun f0 f1 s ->
    let l = Stdlib.String.length s in
    if l = 0 then f0 () else f1 (Stdlib.String.get s 0) (Stdlib.String.sub s 1 (l-1)))
".

From Coq Require Import String Bool Arith ZArith List.

Require Minuska.BuiltinValue Minuska.builtins.

Variant Act := default_act | invisible_act.


#[export]
Instance Act_eqDec : EqDecision Act.
Proof.
    ltac1:(solve_decision).
Defined.

#[export]
Instance DSM
    {mysignature : Signature}
    {β : Model mysignature MyUnit}
    (program_info : ProgramInfo)
    : StaticModel :=
    default_model mysignature β program_info
.

Definition GT {mysignature : Signature} {β : Model mysignature MyUnit} := @TermOver' string (builtin_value).

Definition StepT {mysignature : Signature} {β : Model mysignature MyUnit} (program_info : ProgramInfo) := ProgramT -> NondetValue -> GT -> option GT.
Definition StepT_ext {mysignature : Signature} {β : Model mysignature MyUnit} (program_info : ProgramInfo) := ProgramT -> NondetValue -> GT -> option (GT*nat).

Definition gt_over {mysignature : Signature} {β : Model mysignature MyUnit} (b : builtin_value) : GT := @t_over string builtin_value b.
Definition gt_term {mysignature : Signature} {β : Model mysignature MyUnit} (s : string) (l : list GT) : GT := @t_term string builtin_value s l.

Definition basic_rule
    {mysignature : Signature}
    {β : Model mysignature MyUnit}
    (program_info : ProgramInfo)
    (name : string)
    (l : @TermOver' string StringBuiltinOrVar)
    (r : @TermOver' string StringExpression)
    (cond : StringSideCondition) : Declaration Act
:=
    (decl_rule _ (@mkRuleDeclaration Act name (@mkStringRewritingRule Act l r cond default_act)))
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

Fixpoint sTermOverBoV_subst_gen
    {B : Type}
    (lift_builtin : string -> B)
    (lift_variable : string -> B)
    (t : @TermOver' string StringBuiltinOrVar)
    (x : string)
    (t' : @TermOver' string B)
    : @TermOver' string B
:=
match t with
| t_over (sbov_builtin b) => t_over (lift_builtin b)
| t_over (sbov_var y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (lift_variable y)
    end
| t_term s l => t_term s (map (fun t'' => sTermOverBoV_subst_gen lift_builtin lift_variable t'' x t') l)
end.

Definition sTermOverBoV_subst_expr2
    (t : @TermOver' string StringBuiltinOrVar)
    (x : string)
    (t' : @TermOver' string StringExpression)
    : @TermOver' string StringExpression
:=
    sTermOverBoV_subst_gen (fun b => se_ground (t_over b)) (fun x => se_variable x) t x t'
.

Fixpoint sTermOverBoV_subst
    (t : @TermOver' string StringBuiltinOrVar)
    (x : string)
    (t' : @TermOver' string StringBuiltinOrVar)
:=
match t with
| t_over (sbov_builtin b) => t_over (sbov_builtin b)
| t_over (sbov_var y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (sbov_var y)
    end
| t_term s l => t_term s (map (fun t'' => sTermOverBoV_subst t'' x t') l)
end.

Definition framed_rule
    (frame : (string*(@TermOver' string StringBuiltinOrVar)))
    (name : string)
    (l : @TermOver' string StringBuiltinOrVar)
    (r : @TermOver' string StringExpression)
    (cond : StringSideCondition) : Declaration Act
:=
    (decl_rule _ (@mkRuleDeclaration Act name (@mkStringRewritingRule Act
        (sTermOverBoV_subst frame.2 frame.1 l)
        (sTermOverBoV_subst_expr2 frame.2 frame.1 r)
        cond default_act)))
.

Definition global_naive_interpreter
    {mysignature : Signature}
    {β : Model mysignature MyUnit}
    (program_info : ProgramInfo)
    :=
    @naive_interpreter (DSM program_info) Act
.

Definition global_naive_interpreter_ext
    {mysignature : Signature}
    {β : Model mysignature MyUnit}
    (program_info : ProgramInfo)
    :=
    @naive_interpreter_ext (DSM program_info) Act
.

Definition global_naive_interpreter_sound
    {mysignature : Signature}
    {β : Model mysignature MyUnit}
    (program_info : ProgramInfo)
    :=
    @naive_interpreter_sound (DSM program_info) Act
.
