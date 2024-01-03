From Minuska Require Import
    prelude
    tactics
    spec_syntax
    spec_semantics
    syntax_properties
    basic_matching
.


Definition builtin_value_try_match_BuiltinOrVar
    {Σ : Signature}
    :
    builtin_value -> BuiltinOrVar -> option Valuation :=
fun b bv =>
match bv with
| bov_builtin b' => if (decide (b = b')) then Some ∅ else None
| bov_variable x => Some (<[x := (aoo_operand _ _ b)]>∅)
end.


Definition pure_GroundTerm_try_match_BuiltinOrVar
    {Σ : Signature}
    :
    AppliedOperator' symbol builtin_value -> BuiltinOrVar -> option Valuation
:= fun t bov =>
match bov with
| bov_builtin b => None
| bov_variable x =>
    Some (<[x := (aoo_app _ _ t)]>∅)
end.

