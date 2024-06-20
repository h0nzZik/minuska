From Minuska Require Import
    prelude
    spec
.


Lemma elem_of_next
    {A : Type}
    (x y : A)
    (l : list A)
    :
    x <> y ->
    x ∈ (y::l) ->
    x ∈ l
.
Proof.
    intros. inversion H0; subst; clear H0.
    { ltac1:(contradiction). }
    { assumption. }
Qed.

Section custom_induction_principle_2.

    Context
        {Σ : StaticModel}
        {A : Type}
        {_edA : EqDecision A}
    .

    Lemma TermOver_eqdec : EqDecision (TermOver A).
    Proof.
        ltac1:(unshelve(refine (fix go (t1 t2 : TermOver A) : {t1 = t2} + {t1 <> t2} :=
            match t1 with
            | t_over a1 =>
                match t2 with
                | t_over a2 =>
                    match (decide (a1 = a2)) with
                    | left _ => left _
                    | right _ => right _
                    end
                | t_term _ _ => right _
                end
            | t_term s1 l1 =>
                match t2 with
                | t_over _ => right _
                | t_term s2 l2 =>
                    match (decide (s1 = s2)) with
                    | left _ =>
                    let tmp := (fix go' (l1' l2' : list (TermOver A)) : {l1' = l2'} + {l1' <> l2'} :=
                        match l1' with
                        | [] =>
                            match l2' with
                            | [] => left _
                            | _::_ => right _
                            end
                        | x1::xs1 =>
                            match l2' with
                            | [] => right _
                            | x2::xs2 =>
                                match (go x1 x2) with
                                | left _ =>
                                    match (go' xs1 xs2) with
                                    | left _ => left _
                                    | right _ => right _
                                    end
                                | right _ => right _
                                end
                            end
                        end
                    ) l1 l2 in
                    match tmp with
                    | left _ => left _
                    | right _ => right _
                    end
                    | right _ => right _
                    end
                end
            end
        )); abstract(congruence)).
    Defined.

    Fixpoint TermOver_rect
        (P : TermOver A -> Type)
        (true_for_over : forall a, P (t_over a) )
        (preserved_by_term :
            forall
                (s : symbol)
                (l : list (TermOver A)),
                (forall x, x ∈ l -> P x) ->
                P (t_term s l)
        )
        (p : TermOver A)
    :
        P p :=
    match p with
    | t_over a => true_for_over a
    | t_term s l =>  preserved_by_term s l
        (fun x pf => 
            (fix go (l' : list (TermOver A)) : x ∈ l' -> P x :=
            match l' as l'0 return x ∈ l'0 -> P x with
            | nil => fun pf' => match not_elem_of_nil _ pf' with end
            | y::ys => 
                match (TermOver_eqdec x y) return x ∈ (y::ys) -> P x with
                | left e => fun pf' => (@eq_rect (TermOver A) y P (TermOver_rect P true_for_over preserved_by_term y) x (eq_sym e)) 
                | right n => fun pf' =>
                    let H := @elem_of_next _ _ _ _ n pf' in
                    go ys H
                end
            end
            ) l pf
        )
    end
    .
End custom_induction_principle_2.

#[export]
Existing Instance TermOver_eqdec.
