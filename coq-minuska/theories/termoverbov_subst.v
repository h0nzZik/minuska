From Minuska Require Import
    prelude
    spec
.


Fixpoint TermOverBoV_subst_gen
    {Σ : BackgroundModel}
    {B : Type}
    (lift_builtin : BasicValue -> B)
    (lift_Variabl : Variabl -> B)
    (t : TermOver BuiltinOrVar)
    (x : Variabl)
    (t' : TermOver B)
    : TermOver B
:=
match t with
| t_over (bov_builtin b) => t_over (lift_builtin b)
| t_over (bov_Variabl y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (lift_Variabl y)
    end
| t_term s l => t_term s (map (fun t'' => TermOverBoV_subst_gen lift_builtin lift_Variabl t'' x t') l)
end.

Definition TermOverBoV_subst_expr2
    {Σ : BackgroundModel}
    (t : TermOver BuiltinOrVar)
    (x : Variabl)
    (t' : TermOver Expression2)
    : TermOver Expression2
:=
    TermOverBoV_subst_gen (fun b => e_ground (t_over b)) (fun x => e_Variabl x) t x t'
.

Fixpoint TermOverBoV_subst
    {Σ : BackgroundModel}
    (t : TermOver BuiltinOrVar)
    (x : Variabl)
    (t' : TermOver BuiltinOrVar)
:=
match t with
| t_over (bov_builtin b) => t_over (bov_builtin b)
| t_over (bov_Variabl y) =>
    match (decide (x = y)) with
    | left _ => t'
    | right _ => t_over (bov_Variabl y)
    end
| t_term s l => t_term s (map (fun t'' => TermOverBoV_subst t'' x t') l)
end.

