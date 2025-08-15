From Minuska Require Export
    prelude
    spec
    basic_properties
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
(*
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
*)
From Coq Require Import String Bool Arith ZArith List.

Require Minuska.BuiltinValue Minuska.builtins.

Variant Label := default_label | invisible_label.


#[export]
Instance Label_eqDec : EqDecision Label.
Proof.
    ltac1:(solve_decision).
Defined.
(* 
Print BackgroundModel.
#[export]
Instance DSM
    (* (mysignature : Signature) *)
    (* (hiddensignature : HiddenSignature) *)
    (β : Model mysignature MyUnit)
    (hiddenβ : HiddenModel mysignature hiddensignature β)
    (program_info : ProgramInfo)
    : BackgroundModel :=
    default_model mysignature hiddensignature β hiddenβ program_info
. *)

(* Definition GT {mysignature : Signature} {β : Model mysignature MyUnit} := @TermOver' string (BasicValue).

(* Definition StepT {mysignature : Signature} {β : Model mysignature MyUnit} (program_info : ProgramInfo) := ProgramT -> NondetValue -> GT -> option GT. *)
(* Definition StepT_ext {mysignature : Signature} {β : Model mysignature MyUnit} (program_info : ProgramInfo) := ProgramT -> NondetValue -> GT -> option (GT*nat). *)

Definition gt_over {mysignature : Signature} {β : Model mysignature MyUnit} (b : BasicValue) : GT := @t_over string BasicValue b.
Definition gt_term {mysignature : Signature} {β : Model mysignature MyUnit} (s : string) (l : list GT) : GT := @t_term string BasicValue s l. *)

Definition basic_rule
    (* {mysignature : Signature} *)
    (* {β : Model mysignature MyUnit} *)
    (* (program_info : ProgramInfo) *)
    (name : string)
    (l : @TermOver' string StringBuiltinOrVar)
    (r : @TermOver' string StringExpression)
    (cond : StringSideCondition) : Declaration Label
:=
    (decl_rule _ (@mkRuleDeclaration Label name (@mkStringRewritingRule Label l r cond default_label)))
.



Fixpoint sTermOverBoV_subst_gen
    {B : Type}
    (lift_builtin : BuiltinRepr -> B)
    (lift_Variabl : string -> B)
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
    | right _ => t_over (lift_Variabl y)
    end
| t_term s l => t_term s (map (fun t'' => sTermOverBoV_subst_gen lift_builtin lift_Variabl t'' x t') l)
end.

Definition sTermOverBoV_subst_expr2
    (t : @TermOver' string StringBuiltinOrVar)
    (x : string)
    (t' : @TermOver' string StringExpression)
    : @TermOver' string StringExpression
:=
    sTermOverBoV_subst_gen (fun b => se_ground (t_over b)) (fun x => se_Variabl x) t x t'
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

(* TODO move this to frontend? *)
Definition framed_rule
    (frame : (string*(@TermOver' string StringBuiltinOrVar)))
    (name : string)
    (l : @TermOver' string StringBuiltinOrVar)
    (r : @TermOver' string StringExpression)
    (cond : StringSideCondition) : Declaration Label
:=
    (decl_rule _ (@mkRuleDeclaration Label name (@mkStringRewritingRule Label
        (sTermOverBoV_subst frame.2 frame.1 l)
        (sTermOverBoV_subst_expr2 frame.2 frame.1 r)
        cond default_label)))
.

Definition poly_interpreter
    (BVal HVal NdVal Var Sy Fs Ps As Ms Qs HPs PT : Type)
    (_EBBVal : EDC BVal)
    (_EBHVal : EDC HVal)
    (_EBNdVal : EDC NdVal)
    (_EBVar : EDC Var)
    (_IFVar : Infinite Var)
    (_EBSy : EDC Sy)
    (_EBFs : EDC Fs)
    (_EBPs : EDC Ps)
    (_EBAs : EDC As)
    (_EBMs : EDC Ms)
    (_EBQs : EDC Qs)
    (_EBHPs : EDC HPs)
    (bgm : BackgroundModelOver BVal HVal NdVal Var Sy Fs Ps As Ms Qs HPs PT)
    (Γ : list (@RewritingRule2' BVal Var Sy Fs Qs As Ms Ps HPs Label))
    (program : PT)
    (nv : NdVal)
    (x : (@TermOver' Sy BVal)*(HVal))
    : option ((@TermOver' Sy BVal)*HVal)
:=
    let basic_types := Build_BasicTypes Var Sy Fs Ps HPs As Ms Qs BVal HVal NdVal PT in
    let basic_types_edc := Build_BasicTypesProperties _ _ _ _ _ _ _ _ _ _ _ _ _ in
    let bgm : BackgroundModel := Build_BackgroundModel basic_types basic_types_edc bgm in
    (@naive_interpreter bgm Label Γ program nv x)
.

Definition poly_interpreter_ext
    (BVal HVal NdVal Var Sy Fs Ps As Ms Qs HPs PT : Type)
    (_EBBVal : EDC BVal)
    (_EBHVal : EDC HVal)
    (_EBNdVal : EDC NdVal)
    (_EBVar : EDC Var)
    (_IFVar : Infinite Var)
    (_EBSy : EDC Sy)
    (_EBFs : EDC Fs)
    (_EBPs : EDC Ps)
    (_EBAs : EDC As)
    (_EBMs : EDC Ms)
    (_EBQs : EDC Qs)
    (_EBHPs : EDC HPs)
    (bgm : BackgroundModelOver BVal HVal NdVal Var Sy Fs Ps As Ms Qs HPs PT)
    (Γ : list (@RewritingRule2' BVal Var Sy Fs Qs As Ms Ps HPs Label))
    (program : PT)
    (nv : NdVal)
    (x : (@TermOver' Sy BVal)*(HVal))
    : option ((@TermOver' Sy BVal)*HVal*nat)
:=
    let basic_types := Build_BasicTypes Var Sy Fs Ps HPs As Ms Qs BVal HVal NdVal PT in
    let basic_types_edc := Build_BasicTypesProperties _ _ _ _ _ _ _ _ _ _ _ _ _ in
    let bgm : BackgroundModel := Build_BackgroundModel basic_types basic_types_edc bgm in
    (@naive_interpreter_ext bgm Label Γ program nv x)
.

