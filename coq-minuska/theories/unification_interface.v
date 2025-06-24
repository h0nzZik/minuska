From Minuska Require Import
    prelude
    spec
    basic_properties
.



(* Borrowed from textbook_unification_alg.v. 
   Other functionality not yet required, but may be borrowed
   as well; though then consider some restructuring and possibly importing. *)
Definition eqn {Σ : StaticModel} : Type :=
    ((TermOver BuiltinOrVar)*(TermOver BuiltinOrVar))%type
.

(* 'parallel' substitution *)
Definition SubTMM {Σ : StaticModel} : Type
:=
    gmap variable (TermOver BuiltinOrVar)
.

Fixpoint sub_app_mm {Σ : StaticModel} (s : SubTMM) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match t with
  | t_over (bov_variable v) => let t'_opt := s !! v in
    match t'_opt with
      | None => t
      | Some t' => t'
    end
  | t_term sm l => t_term sm (map (λ t' : TermOver BuiltinOrVar, sub_app_mm s t') l)
  | _ => t
end
.

Definition subtmm_closed {Σ : StaticModel} (s : SubTMM) :=
    forall k v, s !! k = Some v -> vars_of v = ∅
.

Definition is_unifier_of {Σ : StaticModel} (s : SubTMM) (l : list eqn) :=
  Forall (fun '(e1, e2) => sub_app_mm s e1 = sub_app_mm s e2) l
.

Definition SubT {Σ : StaticModel} : Type
:=
    list (variable*(TermOver BuiltinOrVar))%type
.

(* TODO use fold *)
Fixpoint sub_app {Σ : StaticModel} (s : SubT) (t : TermOver BuiltinOrVar) : TermOver BuiltinOrVar :=
match s with
| [] => t
| (x,t')::s' => sub_app s' (TermOverBoV_subst t x t')
end
.

(* TODO use fold *)
Fixpoint subT_to_subTMM
    {Σ : StaticModel}
    (sub : SubT)
    : SubTMM
:=
    match sub with
    | [] => ∅
    | e::es =>
        let subes := subT_to_subTMM es in
        <[e.1 := e.2]>subes
    end
.

Lemma sub_app_mm_empty
    {Σ : StaticModel}
    (φ : TermOver BuiltinOrVar)
    :
    sub_app_mm ∅ φ = φ
.
Proof.
    induction φ; simpl.
    {
        destruct a; simpl.
        { reflexivity. }
        {
            ltac1:(case_match).
            { ltac1:(rewrite lookup_empty in H). inversion H. }
            {
                reflexivity.
            }
        }
    }
    {
        apply f_equal.
        revert H.
        induction l; intros H; simpl in *.
        {
            reflexivity.
        }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            specialize (IHl H2).
            clear H2.
            rewrite H1.
            rewrite IHl.
            reflexivity.
        }
    }
Qed.

Lemma sub_app_app
    {Σ : StaticModel}
    (s1 s2 : SubT)
    (t : TermOver BuiltinOrVar)
:
    sub_app (s1 ++ s2) t = sub_app s2 (sub_app s1 t)
.
Proof.
    revert t.
    induction s1; intros t; simpl.
    { reflexivity. }
    {
        destruct a; simpl in *.
        rewrite IHs1. reflexivity.
    }
Qed.

Lemma sub_app_builtin
    {Σ : StaticModel}
    (ss : SubT)
    (b : builtin_value)
:
    sub_app ss (t_over (bov_builtin b)) = t_over (bov_builtin b)
.
Proof.
    induction ss; simpl.
    { reflexivity. }
    {
        destruct a; simpl in *.
        apply IHss.
    }
Qed.


Lemma sub_app_mm_insert
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    (x : variable)
    (v : TermOver BuiltinOrVar)
    (φ : TermOver BuiltinOrVar)
    :
    subtmm_closed sub_mm  ->
    x ∉ dom sub_mm ->
    sub_app_mm (<[x:=v]>sub_mm) φ
    = sub_app [(x,v)] (sub_app_mm sub_mm φ)
.
Proof.
    induction φ; intros Hsub1 Hxsub; simpl.
    {
        destruct a; simpl.
        {
            reflexivity.
        }
        {
            destruct (decide (x = x0)).
            {
                subst x0.
                ltac1:(rewrite lookup_insert).
                {
                    ltac1:(rewrite not_elem_of_dom_1).
                    { exact Hxsub. }
                    {
                        simpl.
                        rewrite decide_True.
                        { reflexivity. }
                        { reflexivity. }
                    }
                }
            }
            {
                ltac1:(rewrite lookup_insert_ne).
                { assumption. }
                {
                    ltac1:(repeat case_match).
                    {
                        assert (t = t0).
                        {
                            ltac1:(rewrite H in H0).
                            apply (inj Some) in H0.
                            exact H0.
                        }
                        subst t0.
                        symmetry. apply subst_notin2.
                        unfold subtmm_closed in Hsub1.
                        erewrite Hsub1.
                        { ltac1:(set_solver). }
                        { apply H. }
                    }
                    {
                        simpl.
                        rewrite decide_False.
                        {
                            ltac1:(rewrite H0 in H).
                            inversion H.
                        }
                        { assumption. }
                    }
                    {
                        ltac1:(rewrite H0 in H).
                        inversion H.
                    }
                    {
                        simpl.
                        rewrite decide_False.
                        reflexivity.
                        assumption.
                    }
                }
            }
        }
    }
    {
        apply f_equal.
        revert H.
        induction l; intros H; simpl in *.
        { reflexivity. }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite (H1 Hsub1).
            rewrite (IHl H2).
            reflexivity.
            assumption.
        }
    }
Qed.


Lemma subT_to_subTMM_correct
    {Σ : StaticModel}
    (sub : SubT)
    (φ : TermOver BuiltinOrVar)
    :
    sub_app_mm (subT_to_subTMM sub) φ = sub_app sub φ
.
Proof.
    revert φ.
    induction sub; intros φ; simpl.
    {
        rewrite sub_app_mm_empty.
        reflexivity.
    }
    {
        destruct a; simpl in *.


        revert t sub IHsub.
        induction φ; intros t sub IHsub; simpl.
        {
            destruct a; simpl.
            {
                rewrite sub_app_builtin.
                reflexivity.
            }
            {
                destruct (decide (v = x)).
                {
                    subst x.
                    ltac1:(rewrite lookup_insert).
                }
            }
        }
        (* apply IHsub. *)
        rewrite <- IHsub.
        
    }
Qed.

Class UnificationAlgorithm
    {Σ : StaticModel}
:= {
    ua_unify :
        TermOver BuiltinOrVar ->
        TermOver BuiltinOrVar ->
        option SubT
    ;
    
    ua_unify_sound :
        forall
            (t1 t2 : TermOver BuiltinOrVar)
            (u : SubT),
        ua_unify t1 t2 = Some u ->
        (sub_app u t1 = sub_app u t2) /\
        (
            forall u',
                sub_app u' t1 = sub_app u' t2 ->
                exists rest,
                forall (x : variable),
                    sub_app (u ++ rest) (t_over (bov_variable x)) = sub_app u' (t_over (bov_variable x))
        )
    ;

    ua_unify_complete :
        forall (t1 t2 : TermOver BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubT),
                sub_app s t1 <> sub_app s t2
    ;
}.
