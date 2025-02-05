From Minuska Require Import
    prelude
    spec
    basic_properties
    properties
    minusl_syntax
    unification_interface
    (* symex_spec *)
    valuation_merge
.

Locate imap.
Check imap.


Equations? decouple
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    :
    ((TermOver BuiltinOrVar)*(listset (variable * Expression2 )))%type
    by wf (TermOver_size et) lt
:=
    decouple (t_over e) avoid :=
        let y : variable := fresh (avoid) in
        (t_over (bov_variable y), singleton (y,e))
    ;
    decouple (t_term s l) avoid :=
        let l'' := imap (fun (i : nat) (x : TermOver Expression2) =>
            let avoidi := avoid ∪ (union_list (vars_of <$> (take i l))) in
            let pi_sigmai := decouple x avoidi in
            pi_sigmai
        ) l in
    (t_term s (fmap fst l''), union_list (fmap snd l''))
.
Proof.
    Search sum_list
Qed.


Fixpoint decouple
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    :
    ((TermOver BuiltinOrVar)*(listset (variable * Expression2 )))%type
:=
match et with
| t_over e =>
    let y : variable := fresh (avoid) in
    (t_over (bov_variable y), singleton (y,e))
| t_term s l =>
    let l'' := imap (fun (i : nat) (x : TermOver Expression2) =>
        let avoidi := avoid ∪ (union_list (vars_of <$> (take i l))) in
        let pi_sigmai := decouple x avoidi in
        pi_sigmai
    ) l in
    (* let l'' := (fix go
        (l' : list (TermOver Expression2))
        (avoid' : gset variable)
        : list ((TermOver BuiltinOrVar)*(listset (variable * Expression2 )))
        :=
        match l' with
        | [] => []
        | x::xs => 
            let pi := decouple x (avoid' ∪ (vars_of x)) in
            pi::(go xs (avoid' ∪ (vars_of x)))
        end
    ) l avoid in *)
    (t_term s (fmap fst l''), union_list (fmap snd l''))
end
.

Lemma decouple_avoids
    {Σ : StaticModel}
    (et : TermOver Expression2)
    (avoid : gset variable)
    :
    (vars_of (decouple et avoid).1) ## avoid
.
Proof.
    revert avoid.
    induction et;
        intros avoid;
        simpl in *;
        unfold vars_of;
        simpl.
    {
        unfold vars_of; simpl.
        rewrite disjoint_singleton_l.
        rewrite <- elem_of_elements.
        apply infinite_is_fresh.
    }
    {
        revert avoid H.
        induction l; intros avoid H; simpl in *.
        {
            apply disjoint_empty_l.
        }
        {
            rewrite disjoint_union_l.
            rewrite Forall_cons in H.
            destruct H as [Hx Hxs].
            specialize (IHl avoid Hxs).
            clear Hxs.
            split.
            {
                simpl.
                apply Hx.
            }
            {

            }
        }
    }
Qed.