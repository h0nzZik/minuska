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

Definition subt_closed {Σ : StaticModel} (s : SubT) :=
    forall k v, s !! k = Some v -> vars_of v.2 = ∅
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

Fixpoint fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    : list variable
:=
    match n with
    | 0 => []
    | S n' => (fresh avoid)::(fresh_var_seq ((fresh avoid)::avoid) n')
    end
.

Fixpoint fresh_nth
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    : variable
:=
    match n with
    | 0 => fresh avoid
    | S n' => (fresh_nth ((fresh avoid)::avoid) n')
    end
.

Definition renaming_for
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    :
    list (variable*variable)
:=
    let rhss : list (TermOver BuiltinOrVar) := snd <$> map_to_list sub_mm in
    let avoid : list variable := elements (union_list (vars_of <$> rhss)) in
    let to_be_renamed : list variable := elements (dom sub_mm) in
    (* [] *)
    zip to_be_renamed (fresh_var_seq (to_be_renamed ++ avoid) (length to_be_renamed))
.

(* perhaps use kmap? *)
Definition subTMM_to_subT
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    :
    SubT
:=
    let subl : list (variable*(TermOver BuiltinOrVar)) := map_to_list sub_mm in
    let renaming := renaming_for sub_mm in
    let rnmap : gmap variable variable := list_to_map renaming in
    let subl_renamed : list (variable*(TermOver BuiltinOrVar)) := (fun kv => match rnmap !! kv.1 with None => kv | Some y => (kv.1, t_over (bov_variable y)) end) <$> subl in
    subl_renamed ++ ((fun xy => (xy.1, t_over (bov_variable xy.2)))<$> renaming)
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

Lemma sub_app_mm_closed
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of φ = ∅ ->
    sub_app_mm sub_mm φ = φ
.
Proof.
    induction φ; intros HH; simpl in *.
    {
        destruct a; simpl in *.
        { reflexivity. }
        {
            unfold vars_of in HH; simpl in HH.
            unfold vars_of in HH; simpl in HH.
            ltac1:(set_solver).
        }
    }
    {
        apply f_equal.
        revert HH H.
        induction l; intros HH H; simpl in *.
        { reflexivity. }
        {
            rewrite Forall_cons_iff in H.
            destruct H as [H1 H2].
            rewrite vars_of_t_term in HH.
            rewrite fmap_cons in HH.
            rewrite union_list_cons in HH.
            specialize (IHl ltac:(set_solver)).
            specialize (H1 ltac:(set_solver)).
            rewrite H1.
            rewrite (IHl H2).
            reflexivity.
        }
    }
Qed.

Lemma sub_app_mm_insert_2
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    (x : variable)
    (v : TermOver BuiltinOrVar)
    (φ : TermOver BuiltinOrVar)
    :
    vars_of v = ∅ ->
    sub_app_mm (<[x:=v]>sub_mm) φ
    = sub_app_mm sub_mm (sub_app [(x,v)] φ)
.
Proof.
    induction φ; intros Hvars; simpl.
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
                    rewrite sub_app_mm_closed.
                    reflexivity.
                    exact Hvars.
                }
            }
            {
                ltac1:(rewrite lookup_insert_ne).
                { assumption. }
                {
                    ltac1:(repeat case_match).
                    {
                        simpl.
                        ltac1:(rewrite H).
                        reflexivity.
                    }
                    {
                        simpl.
                        ltac1:(rewrite H).
                        reflexivity.
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
            rewrite (H1 Hvars).
            rewrite (IHl H2).
            reflexivity.
        }
    }
Qed.



Lemma subT_to_subTMM_correct
    {Σ : StaticModel}
    (sub : SubT)
    (φ : TermOver BuiltinOrVar)
    :
    subt_closed sub ->
    sub_app_mm (subT_to_subTMM sub) φ = sub_app sub φ
.
Proof.
    revert φ.
    induction sub; intros φ HH; simpl.
    {
        rewrite sub_app_mm_empty.
        reflexivity.
    }
    {
        destruct a; simpl in *.
        rewrite sub_app_mm_insert_2.
        simpl.
        rewrite IHsub.
        { reflexivity. }
        {
            unfold subt_closed in HH.
            unfold subt_closed.
            intros k v0 H1.
            specialize (HH (S k)).
            simpl in HH.
            apply HH.
            assumption.
        }
        {
            unfold subt_closed in HH.
            unfold subt_closed.
            (* intros k v0 H1. *)
            specialize (HH 0 (v,t) eq_refl).
            simpl in HH.
            apply HH.
        }
    }
Qed.

(* Print fresh_var_seq. *)

Lemma elem_of_fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    (x : variable)
    :
    x ∈ fresh_var_seq avoid n ->
    x ∉ avoid
.
Proof.
    revert avoid.
    induction n; intros avoid HH; simpl in *.
    {
        rewrite elem_of_nil in HH.
        destruct HH.
    }
    {
        rewrite elem_of_cons in HH.
        destruct HH as [HH|HH].
        {
            subst x.
            apply infinite_is_fresh.
        }
        {
            specialize (IHn (fresh avoid::avoid) HH).
            ltac1:(set_solver).
        }
    }
Qed.

Lemma NoDup_fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    :
    NoDup (fresh_var_seq avoid n)
.
Proof.
    revert avoid.
    induction n; intros avoid; simpl in *.
    {
        constructor.
    }
    {
        constructor.
        intros HContra.
        apply elem_of_fresh_var_seq in HContra.
        ltac1:(set_solver).
        apply IHn.
    }
Qed.


Lemma subTMM_to_subT_correct
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    (φ : TermOver BuiltinOrVar)
:
    sub_app (subTMM_to_subT sub_mm) φ = sub_app_mm sub_mm φ
.
Proof.
    induction φ.
    {
        simpl.
        destruct a; simpl.
        {
            rewrite sub_app_builtin.
            reflexivity.
        }
        {
            destruct (sub_mm !! x) eqn:Heq.
            {
                unfold subTMM_to_subT.
                rewrite sub_app_app.
                (* Search list_to_map lookup. *)
                simpl.
                assert (Hy: exists y, (((list_to_map (renaming_for sub_mm)):(gmap variable variable)) !! x = Some y)).
                {
                    unfold renaming_for.
                    remember (map_to_list sub_mm) as sub_mm'.
                    remember (snd <$> sub_mm') as rhss.
                    remember (elements (union_list (vars_of <$> rhss))) as avoid.
                    remember (elements (dom sub_mm)) as to_be_renamed.
                    remember (list_find (fun y => x = y) to_be_renamed) as found.
                    destruct found.
                    {

                    }
                    {
                        ltac1:(exfalso).
                        subst.
                        symmetry in Heqfound.
                        ltac1:(rewrite list_find_None in Heqfound).
                        rewrite Forall_forall in Heqfound.
                        specialize (Heqfound x).
                        rewrite elem_of_elements in Heqfound.
                        apply Heqfound.
                        {
                            clear Heqfound.
                            ltac1:(rewrite elem_of_dom).
                            exists t.
                            exact Heq.
                        }
                        {
                            reflexivity.
                        }
                    }
                }
                destruct Hy as [y Hy].
                (* NoDup renaming ? *)
(*                 
                assert(((list_to_map (renaming_for sub_mm)):(gmap variable variable)) !! y = None).
                {
                    (* clear Hy Heq. *)
                    unfold renaming_for.
                    apply not_elem_of_list_to_map_1.
                    intros HContra.
                    (* unfold zip. *)
                    rewrite elem_of_list_fmap in HContra.
                    destruct HContra as [z [H1z H2z]].
                    destruct z as [z1 z2].
                    simpl in *. subst.
                    apply elem_of_zip_l in H2z as H1.
                    apply elem_of_zip_r in H2z as H2.
                    clear H2z.

                    apply elem_of_fresh_var_seq in H2.
                    
                    rewrite elem_of_elements in H1.
                    ltac1:(rewrite elem_of_dom in H1).
                    destruct H1 as [t' Ht'].
                    
                    rewrite elem_of_app in H2.
                    rewrite elem_of_elements in H2.
                    apply Decidable.not_or in H2.
                    destruct H2 as [H21 H22].
                    Search (~ (_ \/ _)).
                    Search elem_of zip.
                    ltac1:(rewrite elem_of_zip_with in H2z).
                    (* Search (list_to_map _ !! _ = None). *)
                } *)

                lazy_match! goal with
                | [|- sub_app _ ?s = _] =>
                    (* unfold SubTMM in *; *)
                    assert(H1: $s = t_over (bov_variable y))
                end.
                {
                    (* ltac1:(induction sub_mm using map_ind). *)
                    remember (map_to_list sub_mm) as sub_mm'.
                    assert (Hnd := stdpp.fin_maps.map_to_list_spec sub_mm).
                    ltac1:(rewrite - Heqsub_mm' in Hnd).
                    
                    assert (Hxt: (x,t) ∈ sub_mm').
                    {
                        subst sub_mm'.
                        ltac1:(rewrite elem_of_map_to_list).
                        exact Heq.
                    }
                    clear Heqsub_mm' Heq.
                    revert Hnd Hxt.
                    induction sub_mm'; intros Hnd Hxt; simpl in *.
                    {
                        rewrite elem_of_nil in Hxt.
                        inversion Hxt.
                    }
                    {
                        rewrite elem_of_cons in Hxt.
                        destruct Hxt as [Hxt|Hxt].
                        {
                            subst a.
                            ltac1:(rewrite Hy).
                            simpl in *.
                            rewrite decide_True.
                            {
                                clear IHsub_mm'.
                                rewrite NoDup_cons in Hnd.
                                destruct Hnd as [[Hnd1 Hnd2] Hnd3].
                                assert (x ∉ dom sub_mm).
                                {
                                    ltac1:(rewrite elem_of_dom).
                                    intros HContra.
                                    destruct HContra as [z Hz].
                                    rewrite <- Hnd3 in Hz.
                                    rewrite elem_of_cons in Hz.
                                    destruct (decide (z = t)).
                                    {
                                        destruct Hz as [Hz|Hz];
                                            try ltac1:(naive_solver).
                                        ltac1:(simplify_eq/=).
                                        apply Hnd1.
                                    }
                                }
(* 
                                assert (Htmp := proj1 (Hnd3 x t)).
                                rewrite elem_of_cons in Htmp.
                                ltac1:(ospecialize (Htmp _)).
                                {
                                    left. reflexivity.
                                } *)
                                (* This becomes wild *)
                                revert Hnd1 Hnd2 Hnd3. clear Hy.
                                induction sub_mm';
                                    intros Hnd1 Hnd2 Hnd3;
                                    simpl in *.
                                {
                                    reflexivity.
                                }
                                {
                                    simpl in *.
                                    ltac1:(repeat case_match).
                                    {
                                        ltac1:(simplify_eq/=).
                                    }
                                    {

                                    }
                                }



                                simpl.
                                Search sub_app.
                                (* lazy_match! goal with
                                | [|- sub_app ?s _ = _] =>

                                end. *)
                            }
                            {
                                reflexivity.
                            }
                        }
                    }
                    Search map_to_list elem_of.
                    (* assert (Hxt: (x,t) ∈ ) *)
                }
                Search sub_app bov_variable.
            }
            {
                simpl.
            }
        }
    }
Qed.

Class UnificationAlgorithm
    {Σ : StaticModel}
:= {
    ua_unify :
        TermOver BuiltinOrVar ->
        TermOver BuiltinOrVar ->
        option SubTMM
    ;
    
    ua_unify_sound :
        forall
            (t1 t2 : TermOver BuiltinOrVar)
            (u : SubTMM),
        ua_unify t1 t2 = Some u ->
        (sub_app_mm u t1 = sub_app_mm u t2) /\
        (
            forall (u' : SubTMM),
                sub_app_mm u' t1 = sub_app_mm u' t2 ->
                    map_subseteq u u'
        )
    ;

    ua_unify_complete :
        forall (t1 t2 : TermOver BuiltinOrVar),
            ua_unify t1 t2 = None ->
            forall (s : SubTMM),
                sub_app_mm s t1 <> sub_app_mm s t2
    ;
}.
