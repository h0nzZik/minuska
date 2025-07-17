From Minuska Require Import
    prelude
    spec
.


Fixpoint TermOverBoV_subst_gen
    {Σ : StaticModel}
    {B : Type}
    (lift_builtin : builtin_value -> B)
    (lift_variable : variable -> B)
    (t : TermOver BuiltinOrVar)
    (x : variable)
    (t' : TermOver B)
    : TermOver B
:=
match t with
| t_over (bov_builtin b) => t_over (lift_builtin b)
| t_over (bov_variable y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (lift_variable y)
    end
| t_term s l => t_term s (map (fun t'' => TermOverBoV_subst_gen lift_builtin lift_variable t'' x t') l)
end.

Definition TermOverBoV_subst_expr2
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (x : variable)
    (t' : TermOver Expression2)
    : TermOver Expression2
:=
    TermOverBoV_subst_gen (fun b => e_ground (t_over b)) (fun x => e_variable x) t x t'
.

Fixpoint TermOverBoV_subst
    {Σ : StaticModel}
    (t : TermOver BuiltinOrVar)
    (x : variable)
    (t' : TermOver BuiltinOrVar)
:=
match t with
| t_over (bov_builtin b) => t_over (bov_builtin b)
| t_over (bov_variable y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (bov_variable y)
    end
| t_term s l => t_term s (map (fun t'' => TermOverBoV_subst t'' x t') l)
end.

