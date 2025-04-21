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
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (cond : SideCondition) : Declaration
:=
    (decl_rule (@mkRuleDeclaration (DSM program_info) Act name (@mkRewritingRule2 (DSM program_info) Act l r cond default_act)))
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
    {mysignature : Signature}
    {β : Model mysignature MyUnit}
    (program_info : ProgramInfo)
    (frame : (variable*(TermOver BuiltinOrVar)))
    (name : string)
    (l : TermOver BuiltinOrVar)
    (r : TermOver Expression2)
    (cond : SideCondition) : Declaration
:=
    (decl_rule (@mkRuleDeclaration (DSM program_info) Act name (@mkRewritingRule2 (DSM program_info) Act
        (TermOverBoV_subst frame.2 frame.1 l)
        (TermOverBoV_subst_expr2 frame.2 frame.1 r)
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
