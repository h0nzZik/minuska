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

Lemma length_fresh_var_seq
    {Σ : StaticModel}
    (avoid : list variable)
    (n : nat)
    :
    length (fresh_var_seq avoid n) = n
.
Proof.
    revert avoid.
    induction n; intros avoid; simpl in *.
    { reflexivity. }
    {
        rewrite IHn. reflexivity.
    }
Qed.

Lemma NoDup_1_renaming_for
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    :
    NoDup (fst <$> renaming_for sub_mm)
.
Proof.
    unfold renaming_for.
    rewrite fst_zip.
    {
        apply NoDup_elements.
    }
    {
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma NoDup_2_renaming_for
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    :
    NoDup (snd <$> renaming_for sub_mm)
.
Proof.
    unfold renaming_for.
    rewrite snd_zip.
    {
        apply NoDup_fresh_var_seq.
    }
    {
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.

Lemma NoTwice_renaming_for
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    :
    forall (x : variable),
        x ∈ (snd <$> renaming_for sub_mm) ->
        x ∉ (fst <$> renaming_for sub_mm)
.
Proof.
    unfold renaming_for.
    remember (length (elements (dom sub_mm))) as n.
    intros x Hx HContra.
    rewrite elem_of_list_fmap in HContra.
    destruct HContra as [[y z] [H1 H2]].
    apply elem_of_zip_l in H2 as H2l.
    apply elem_of_zip_r in H2 as H2r.
    clear H2.
    subst x.
    simpl in *.
    rewrite elem_of_list_fmap in Hx.
    destruct Hx as [[x y1][H3 H4]].
    simpl in *.
    subst y1.
    apply elem_of_zip_l in H4 as Hx1.
    apply elem_of_zip_r in H4 as Hx2.
    clear H4.
    apply elem_of_fresh_var_seq in Hx2.
    clear - Hx2 H2l.
    ltac1:(set_solver).
Qed.

Lemma renaming_for_all
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    :
    elements (dom sub_mm) ⊆ (fst <$> (renaming_for sub_mm))
.
Proof.
    unfold renaming_for.
    ltac1:(rewrite elem_of_subseteq).
    intros x Hx.
    rewrite fst_zip.
    {
        exact Hx.
    }
    {
        rewrite length_fresh_var_seq.
        ltac1:(lia).
    }
Qed.
(* 
Lemma elem_of_zip_both
    {A B : Type}
    (a : A)
    (b : B)
    (la : list A)
    (lb : list B)
:
    length la = length lb ->
    a ∈ la ->

    (a,b) ∈ zip la lb
. *)
(* 
Lemma elements_union_produce
    {A : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (g : gset A)
:
    (elements g = [])
    \/
    (∃ a, elements g = a::(elements (g ∖ {[a]})))
.
Proof.
    destruct (decide (elements g = [])) as [?|Hg].
    {
        left.
        assumption.
    }
    {
        right.
        destruct (elements g) eqn:Heqeg.
        {
            ltac1:(contradiction Hg).
            reflexivity.
        }
        {
            clear Hg.
            unfold elements in *.
            unfold gset_elements in *.
            unfold mapset.mapset_elements in *.
            (* rewrite <- Heqeg. *)
            destruct g as [m].
            simpl in *.
            exists a.
            apply f_equal.
            destruct m as [car].
            destruct car.
            {
                simpl in *.
                inversion Heqeg.
            }
            {
                unfold map_to_list in *.
                unfold map_fold in *.
                unfold gmap_fold in *.
                unfold gmap.gmap_dep_fold in *.
                unfold gmap.gmap_dep_ne_fold in *.
                rewrite Heqeg.
                (* unfold gmap.gmap_fold_aux in *. *)
                simpl in *.
                
                destruct g; simpl in *;
                unfold difference;
                unfold map_difference;
                unfold difference_with;
                unfold map_difference_with;
                unfold merge;
                unfold gmap_merge;
                simpl in *;
                ltac1:(repeat case_match; simplify_eq/=).
                {
                    inversion H; subst; clear H; simpl in *.
                }
            }
            simpl in *.
            (* rewrite Heqeg. *)
            remember ((map_to_list g).*1) as m'.
            assert (Htmp2 := elements_union_singleton (g ∖ {[a]}) a ltac:(set_solver)).
            inversion Htmp2; subst; clear Htmp2.
            {
                exists a.
                apply f_equal.
                assert (H0: a ∈ g).
                {
                    rewrite <- elem_of_elements.
                    rewrite Heqeg.
                    rewrite elem_of_cons.
                    left.
                    reflexivity.
                }
                assert (Htmp : {[a]} ∪ (g ∖ {[a]}) = g).
                {
                    assert (Htmp2 := union_difference_singleton a g H0).
                    ltac1:(set_solver).
                }
                rewrite Htmp in H.
                rewrite Heqeg in H.
                inversion H; subst; clear H.
                ltac1:(simplify_eq/=).
            }
            {

            }
            {

            }
        }
        Search not nil.
    }
   remember (size g) as sz.
    assert (Hsz : size g <= sz) by ltac1:(lia).
    clear Heqsz.
    revert g Hsz.
    induction (sz); intros g Hsz.
    {
        assert (H0 : size g = 0) by ltac1:(lia).
        apply size_empty_inv in H0.
        assert(g = ∅) by ltac1:(set_solver).
        subst g.
        left.
        rewrite elements_empty.
        reflexivity.
    }
    {
        destruct (size g) eqn:Heqsz.
        {
            assert (H0 : size g = 0) by ltac1:(lia).
            apply size_empty_inv in H0.
            assert(g = ∅) by ltac1:(set_solver).
            subst g.
            left.
            rewrite elements_empty.
            reflexivity.
        }
        {
            assert (Hsz': n <= sz) by ltac1:(lia).
            assert (Hsz'' : 0 < size g) by ltac1:(lia).
            apply size_pos_elem_of in Hsz''.
            destruct Hsz'' as [x Hx].
            apply union_difference_singleton_L in Hx as Hx'.
            right.
            assert (IHsz' := IHsz (g ∖ {[x]})).
            ltac1:(ospecialize (IHsz' _)).
            {
                rewrite size_difference.
                rewrite size_singleton.
                ltac1:(lia).
                ltac1:(set_solver).
            }
            destruct IHsz' as [IHsz'|IHsz'].
            {
                apply elements_empty_inv in IHsz'.
                exists x.
                assert(Hgx : g ∖ {[x]} = ∅) by ltac1:(set_solver).
                rewrite Hgx.
                rewrite elements_empty.
                assert (Hgx' : g = {[x]}) by ltac1:(set_solver).
                rewrite Hgx'.
                rewrite elements_singleton.
                reflexivity.
            }
            {
                destruct IHsz' as [a Ha].
                ltac1:(setoid_rewrite Hx' at 1).
                assert (Htmp2 := elements_union_singleton (g ∖ {[x]}) x ltac:(set_solver)).
                inversion Htmp2; subst; clear Htmp2.
                {
                    exists x.
                    apply f_equal.
                    rewrite Ha.
                }
                Search elements union.
                destruct (decide (x = a)).
                {
                    subst x.
                    exists a.
                    rewrite Ha.
                }
                (* exists a. *)
                (* rewrite *)

            }
        }
    }
 
Qed.


Lemma elements_union_singleton_produce
    {A : Type}
    {_EA : EqDecision A}
    {_CA : Countable A}
    (a : A)
    (g : gset A)
:
    a ∉ g ->
    (elements ({[a]} ∪ g) = a::(elements g))
    \/
    (∃ b rest, g = {[b]} ∪ rest /\ elements ({[a]} ∪ g) = b::(elements rest))
.
Proof.
    remember (size g) as sz.
    assert (Hsz : size g <= sz) by ltac1:(lia).
    clear Heqsz.
    revert a g Hsz.
    induction (sz); intros a g Hsz Hnotin.
    {
        assert (H0 : size g = 0) by ltac1:(lia).
        apply size_empty_inv in H0.
        assert(g = ∅) by ltac1:(set_solver).
        subst g.
        rewrite union_empty_r_L.
        rewrite elements_empty.
        rewrite elements_singleton.
        left.
        reflexivity.
    }
    {
        destruct (size g) eqn:Heqsz.
        {
            assert (H0 : size g = 0) by ltac1:(lia).
            apply size_empty_inv in H0.
            assert(g = ∅) by ltac1:(set_solver).
            subst g.
            rewrite union_empty_r_L.
            rewrite elements_empty.
            rewrite elements_singleton.
            left.
            reflexivity.
        }
        {
            assert (Hsz': n <= sz) by ltac1:(lia).
            assert (Hsz'' : 0 < size g) by ltac1:(lia).
            apply size_pos_elem_of in Hsz''.
            destruct Hsz'' as [x Hx].
            destruct (decide (x = a)).
            {
                subst x.
                ltac1:(exfalso).
                apply Hnotin.
                apply Hx.
            }
            {
                (* assert (Ha := union_difference_singleton_L a (g ∖ {[a]})).
                ltac1:(ospecialize (Ha _)).
                {

                } *)
                (* Search difference elem_of. *)
                apply union_difference_singleton_L in Hx as Hx'.
                assert (IHa := IHsz a (g ∖ {[x]})).
                ltac1:(ospecialize (IHa _ _)).
                {
                    rewrite size_difference.
                    rewrite size_singleton.
                    ltac1:(lia).
                    ltac1:(set_solver).
                }
                {
                    ltac1:(set_solver).
                }
                (* rewrite Hx'. *)
                destruct IHa as [IHa|IHa].
                {
                    ltac1:(setoid_rewrite Hx' at 3 4).
                    left.
                    (* rewrite Hx' at 2. *)
                    (* rewrite <- IHa. *)
                    (* ltac1:(set_solver). *)
                }
                {

                }
                
                Search elem_of difference.
            }
        {
            Search size elem_of.
        }
        
        destruct (decide (x = a)).
        {
            subst x.
            ltac1:(exfalso).
            clear - Hnotin.
            ltac1:(set_solver).
        }
        {
            assert (IHx := IHg x H).
            assert (IHa := IHg a ltac:(set_solver)).
            destruct IHx as [IHx|IHx],
                IHa as [IHa|IHa].
            {
                rewrite IHx.
                left.

                rewrite IHg.
            }
        }
    }
Qed. *)


Lemma subTMM_to_subT_correct
    {Σ : StaticModel}
    (sub_mm : SubTMM)
    (φ : TermOver BuiltinOrVar)
:
    sub_app (subTMM_to_subT sub_mm) φ = sub_app_mm sub_mm φ
.
Proof.
    unfold subTMM_to_subT.
    remember (renaming_for sub_mm) as rn.
    unfold renaming_for in Heqrn.
    remember ((elements (dom sub_mm) ++ elements (⋃ (vars_of <$> (map_to_list sub_mm).*2)))) as avoid.
    assert (Havoid : ((elements (dom sub_mm) ++ elements (⋃ (vars_of <$> (map_to_list sub_mm).*2)))) ⊆ avoid) by ltac1:(set_solver).
    clear Heqavoid.

    subst rn.
    revert avoid Havoid.
    induction φ; intros avoid Havoid.
    {
        simpl in *.
        destruct a.
        {
            simpl in *.
            rewrite sub_app_builtin.
            reflexivity.
        }
        {
            remember (map_to_list sub_mm) as sub_mm'.
            
            assert (Hlen: (length (elements (dom (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _ sub_mm')))) = length sub_mm').
            {
                rewrite dom_list_to_map.
                rewrite elements_list_to_set.
                rewrite length_fmap.
                reflexivity.
                subst sub_mm'.
                unfold SubTMM in *.
                apply NoDup_fst_map_to_list.
            }
            
            assert (Hsub_mm'_nodup : NoDup (fst <$> sub_mm')).
            {
                subst sub_mm'.
                unfold SubTMM in *.
                apply NoDup_fst_map_to_list.
            }
            ltac1:(apply (f_equal (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _)) in Heqsub_mm').
            ltac1:(rewrite list_to_map_to_list in Heqsub_mm').
            subst sub_mm.
            ltac1:(rewrite Hlen).
            clear Hlen.
            revert avoid Havoid.
            induction sub_mm'; intros avoid Havoid.
            {
                simpl in *.
                ltac1:(rewrite lookup_empty dom_empty_L elements_empty).
                simpl.
                reflexivity.
            }
            {
                simpl.
                destruct a as [y t].
                simpl in *.
                destruct (decide (x = y)).
                {
                    subst y.
                    ltac1:(rewrite lookup_insert).
                    destruct (list_to_map
                        (zip (elements (dom (<[x:=t]> (list_to_map sub_mm'))))
                        (fresh avoid
                        :: fresh_var_seq (fresh avoid :: avoid) (length sub_mm')))
                        !! x
                    ) eqn:Heq1.
                    {
                        fold (@fmap list list_fmap) in *.
                        rewrite decide_True>[|reflexivity].
                        (* rewrite sub_app_app. *)
                        ltac1:(ospecialize (IHsub_mm' _)).
                        {
                            inversion Hsub_mm'_nodup; subst.
                            assumption.
                        }
                        specialize (IHsub_mm' (fresh avoid :: avoid)).
                        ltac1:(ospecialize (IHsub_mm' _)).
                        {
                            ltac1:(rewrite dom_list_to_map).
                            ltac1:(rewrite dom_insert_L in Havoid).
                            ltac1:(rewrite dom_list_to_map in Havoid).
                            ltac1:(set_solver).
                        }
                        rewrite sub_app_app.
                        rewrite sub_app_app in IHsub_mm'.
                        lazy_match! goal with
                        | [ |- sub_app _ ?p = _] =>
                            assert (exists z, $p = t_over (bov_variable z) /\ z ∈ (fresh avoid :: fresh_var_seq (fresh avoid :: avoid) (length sub_mm')))
                        end.
                        {
                            clear - Heq1 Hsub_mm'_nodup.
                            revert v avoid Heq1 Hsub_mm'_nodup.
                            induction sub_mm'; intros v avoid Heq1 Hsub_mm'_nodup.
                            {
                                simpl in *.
                                exists v.
                                split>[reflexivity|].
                                ltac1:(rewrite dom_insert_L in Heq1).
                                ltac1:(rewrite union_empty_r_L in Heq1).
                                rewrite elements_singleton in Heq1.

                                ltac1:(rewrite - elem_of_list_to_map in Heq1).
                                {
                                    constructor.
                                    intros HContra.
                                    rewrite elem_of_nil in HContra.
                                    exact HContra.
                                    constructor.
                                }
                                simpl in Heq1.
                                rewrite elem_of_cons.
                                rewrite elem_of_cons in Heq1.
                                ltac1:(set_solver).
                            }
                            {
                                simpl in *.


                                (* I have to find a different variable than [v] *)
                                ltac1:(setoid_rewrite <- elem_of_list_to_map in IHsub_mm').
                                ltac1:(setoid_rewrite elem_of_list_lookup in IHsub_mm').
                                ltac1:(rewrite dom_insert_L in IHsub_mm').
                                assert(Htmp: ∃ i' v', zip (elements ({[x]} ∪ dom (@list_to_map variable (TermOver BuiltinOrVar) (gmap (variable) (TermOver BuiltinOrVar)) _ _ sub_mm')))
                                        (fresh avoid
                                                :: fresh_var_seq (fresh avoid :: avoid)
                                                (length sub_mm'))
                                                !! i' =
                                        Some (x, v')).
                                {
                                    remember (list_find (eq x) (elements ({[x]} ∪ dom (@list_to_map variable (TermOver BuiltinOrVar) (gmap (variable) (TermOver BuiltinOrVar)) _ _ sub_mm')))) as found.
                                    destruct found.
                                    {
                                        symmetry in Heqfound.
                                        destruct p as [j v'].
                                        rewrite list_find_Some in Heqfound.
                                        destruct Heqfound as [HH1 [HH2 HH3]].
                                        subst v'.
                                        destruct ((fresh avoid :: fresh_var_seq (fresh avoid :: avoid) (length sub_mm')) !! j) eqn:Heq2.
                                        {
                                            exists j, v0.
                                            (* TODO *)
                                            Search
                                        }
                                        {
                                            ltac1:(exfalso).
                                            apply lookup_lt_Some in HH1.
                                            rewrite elements_union_singleton in HH1.
                                            simpl in HH1.
                                            apply lookup_ge_None in Heq2.
                                            simpl in Heq2.
                                            rewrite length_fresh_var_seq in Heq2.
                                            rewrite dom_list_to_map in HH1.
                                            rewrite elements_list_to_set in HH1.
                                            {
                                                rewrite length_fmap in HH1.
                                                ltac1:(lia).
                                            }
                                            {
                                                inversion Hsub_mm'_nodup;
                                                subst;
                                                clear Hsub_mm'_nodup.
                                                inversion H2; subst; clear H2.
                                                assumption.
                                            }
                                            rewrite elem_of_dom.
                                            intros [p Hp].
                                            ltac1:(rewrite - elem_of_list_to_map in Hp).
                                            {
                                                inversion Hsub_mm'_nodup;
                                                subst;
                                                clear Hsub_mm'_nodup.
                                                inversion H2; subst; clear H2.
                                                assumption.
                                            }
                                            {
                                                inversion Hsub_mm'_nodup;
                                                subst;
                                                clear Hsub_mm'_nodup.
                                                inversion H2; subst; clear H2.
                                                apply H1. clear H1.
                                                rewrite elem_of_cons.
                                                right.
                                                rewrite elem_of_list_fmap.
                                                exists (x, p).
                                                split>[reflexivity|].
                                                exact Hp.
                                            }
                                        }
                                    }
                                    {
                                        ltac1:(exfalso).
                                        symmetry in Heqfound.
                                        rewrite list_find_None in Heqfound.
                                        rewrite Forall_forall in Heqfound.
                                        specialize (Heqfound x ltac:(set_solver)).
                                        apply Heqfound.
                                        reflexivity.
                                    }
                                }
                                destruct Htmp as [i' [v' Htmp]].
                                specialize (IHsub_mm' v' avoid).
                                ltac1:(ospecialize (IHsub_mm' _ _)).
                                {
                                    exists i'.
                                    apply Htmp.
                                }
                                {
                                    rewrite NoDup_cons.
                                    rewrite NoDup_cons in Hsub_mm'_nodup.
                                    rewrite NoDup_cons in Hsub_mm'_nodup.
                                    ltac1:(set_solver).
                                }
                                destruct IHsub_mm' as [z [H1z H2z]].
                                exists z.
                                fold (@fmap list list_fmap) in *.
                                ltac1:(case_match).
                                {
                                    Search a.
                                }
                                {

                                }


                                specialize (IHsub_mm' v (avoid)).
                                simpl in *.
                                ltac1:(ospecialize (IHsub_mm' _)).
                                {
                                    ltac1:(rewrite - elem_of_list_to_map in Heq1).
                                    {
                                        repeat (rewrite NoDup_cons in Hsub_mm'_nodup).
                                        destruct Hsub_mm'_nodup as [HH1 [HH2 HH3]].
                                        rewrite fst_zip.
                                        apply NoDup_elements.
                                        simpl.
                                        rewrite length_fresh_var_seq.
                                        ltac1:(rewrite dom_insert_L).
                                        ltac1:(rewrite dom_insert_L).
                                        rewrite elements_union_singleton.
                                        {
                                            rewrite elements_union_singleton.
                                            {
                                                simpl.
                                                ltac1:(rewrite dom_list_to_map).
                                                rewrite elements_list_to_set.
                                                rewrite length_fmap.
                                                ltac1:(lia).
                                                assumption.
                                            }
                                            {
                                                fold (@fmap list list_fmap) in *.
                                                intros HContra.
                                                apply HH2. clear HH2.
                                                rewrite elem_of_dom in HContra.
                                                destruct HContra as [b Hb].
                                                rewrite elem_of_list_fmap.
                                                destruct a as [a1 a2].
                                                simpl in *.
                                                exists (a1, b).
                                                split>[reflexivity|].
                                                ltac1:(rewrite - elem_of_list_to_map in Hb).
                                                { exact HH3. }
                                                { exact Hb. }
                                            }    
                                        }
                                        {
                                            intros HContra.
                                            rewrite elem_of_union in HContra.
                                            destruct HContra as [HContra|HContra].
                                            {
                                                rewrite elem_of_singleton in HContra.
                                                subst x.
                                                fold (@fmap list list_fmap) in *.
                                                apply HH1.
                                                clear HH1.
                                                rewrite elem_of_cons.
                                                left.
                                                reflexivity.
                                            }
                                            {
                                                fold (@fmap list list_fmap) in *.
                                                rewrite elem_of_dom in HContra.
                                                destruct HContra as [b Hb].
                                                ltac1:(rewrite - elem_of_list_to_map in Hb).
                                                { exact HH3. }
                                                apply HH1.
                                                rewrite elem_of_cons.
                                                clear HH1.
                                                right. 
                                                rewrite elem_of_list_fmap.
                                                exists (x,b).
                                                split>[reflexivity|].
                                                exact Hb.
                                            }
                                        }
                                    }
                                    ltac1:(rewrite - elem_of_list_to_map).
                                    {
                                        simpl in *.
                                        repeat (rewrite NoDup_cons in Hsub_mm'_nodup).
                                        destruct Hsub_mm'_nodup as [HH1 [HH2 HH3]].
                                        rewrite fst_zip.
                                        ltac1:(rewrite dom_insert_L).
                                        ltac1:(rewrite elements_union_singleton).
                                        {
                                            fold (@fmap list list_fmap) in *.
                                            intros HContra.
                                            apply HH1.
                                            clear HH1.
                                            rewrite elem_of_cons.
                                            right.
                                            rewrite elem_of_list_fmap.
                                            rewrite elem_of_dom in HContra.
                                            destruct HContra as [p Hp].
                                            exists (x, p).
                                            split>[reflexivity|].
                                            ltac1:(rewrite - elem_of_list_to_map in Hp).
                                            { assumption. }
                                            { exact Hp. }
                                        }
                                        {
                                            rewrite NoDup_cons.
                                            fold (@fmap list list_fmap) in *.
                                            rewrite elem_of_elements.
                                            rewrite elem_of_dom.
                                            split.
                                            {
                                                intros HContra.
                                                destruct HContra as [p Hp].
                                                ltac1:(rewrite - elem_of_list_to_map in Hp).
                                                { assumption. }
                                                apply HH1. clear HH1.
                                                rewrite elem_of_cons.
                                                right.
                                                rewrite elem_of_list_fmap.
                                                exists (x, p).
                                                split>[reflexivity|].
                                                exact Hp.
                                            }
                                            {
                                                apply NoDup_elements.
                                            }
                                        }
                                        {
                                            simpl.
                                            ltac1:(rewrite dom_insert).
                                            rewrite elements_union_singleton.
                                            simpl.
                                            rewrite length_fresh_var_seq.
                                            ltac1:(rewrite dom_list_to_map_L).
                                            ltac1:(rewrite elements_list_to_set).
                                            assumption.
                                            rewrite length_fmap.
                                            ltac1:(lia).
                                            intros HContra.
                                            rewrite elem_of_dom in HContra.
                                            destruct HContra as [p Hp].
                                            ltac1:(rewrite - elem_of_list_to_map in Hp).
                                            assumption.
                                            fold (@fmap list list_fmap) in *.
                                            apply HH1.
                                            clear HH1.
                                            rewrite elem_of_cons.
                                            right.
                                            rewrite elem_of_list_fmap.
                                            exists (x,p).
                                            simpl.
                                            split>[reflexivity|].
                                            exact Hp.
                                        }
                                    }
                                    rewrite elem_of_list_lookup.
                                    rewrite elem_of_list_lookup in Heq1.
                                    destruct Heq1 as [i Hi].
                                    Search elem_of zip(* HERE *).
                                }
                            }
                        }
                        assert(Htmp :
                        
                        ).
                        rewrite IHsub_mm'.
                        
                    }
                    
                }
            }
        }
    }
Qed.


Lemma subTMM_to_subT_correct1
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
                (* assert (Hnd := NoDup_2_renaming_for sub_mm). *)
                (* NoDup renaming ? *)

                lazy_match! goal with
                | [|- sub_app _ ?s = _] =>
                    (* unfold SubTMM in *; *)
                    assert(H1: $s = t_over (bov_variable y))
                end.
                {
                    (* unfold renaming_for in *. *)
                    remember (map_to_list sub_mm) as sub_mm'.
                    assert (Hsub_mm'_nodup : NoDup (fst <$> sub_mm')).
                    {
                        subst sub_mm'.
                        unfold SubTMM in *.
                        apply NoDup_fst_map_to_list.
                    }
                    ltac1:(apply (f_equal (@list_to_map variable (TermOver BuiltinOrVar) (gmap variable (TermOver BuiltinOrVar)) _ _)) in Heqsub_mm').
                    ltac1:(rewrite list_to_map_to_list in Heqsub_mm').
                    
                    clear Heq t.
                    subst sub_mm.

                    revert x y Hy Hsub_mm'_nodup.
                    induction sub_mm'; intros x y Hy Hsub_mm'_nodup; simpl in *.
                    {
                        apply elem_of_list_to_map_2 in Hy.
                        unfold renaming_for in Hy.
                        apply elem_of_zip_l in Hy.
                        ltac1:(rewrite dom_empty_L in Hy).
                        rewrite elements_empty in Hy.
                        rewrite elem_of_nil in Hy.
                        destruct Hy.
                    }
                    {
                        lazy_match! Constr.type &Hy with
                        | (list_to_map ?a) !! _ = _ => remember $a as m
                        end.
                        destruct a as [z t'].
                        simpl in *.
                        destruct (list_to_map m !! z) eqn:Hma.
                        {
                            destruct (decide (z = x)).
                            {
                                subst z.
                                rewrite Hma in Hy.
                                apply (inj Some) in Hy.
                                subst v.
                                rewrite Heqm in Hma.
                                (* Search lookup list_to_map. *)
                                ltac1:(rewrite <- elem_of_list_to_map in Hma).
                                assert(Hnt := NoTwice_renaming_for (<[x:=t']> (list_to_map sub_mm')) y).
                                rewrite elem_of_list_fmap in Hnt.
                                ltac1:(ospecialize (Hnt _)).
                                {
                                    exists (x,y).
                                    simpl.
                                    split>[reflexivity|].
                                    apply Hma.
                                }

                                (* UFF *)
                                (* Search renaming_for. *)
                                (* Check renaming_for_all. *)
                                clear IHsub_mm'.
                                assert (Hra := renaming_for_all  (<[x:=t']> (list_to_map sub_mm'))).
                                assert (Hra' : (fst <$> sub_mm') ⊆ (renaming_for (<[x:=t']> (list_to_map sub_mm'))).*1).
                                {
                                    ltac1:(rewrite elem_of_subseteq).
                                    ltac1:(rewrite elem_of_subseteq in Hra).
                                    intros x0 Hx0.
                                    specialize (Hra x0).
                                    ltac1:(ospecialize (Hra _)).
                                    {
                                        rewrite elem_of_elements.
                                        ltac1:(rewrite elem_of_dom).
                                        rewrite elem_of_list_fmap in Hx0.
                                        destruct Hx0 as [[z phi] [H2 H3]].
                                        subst x0. simpl in *.
                                        destruct (decide (z = x)).
                                        {
                                            subst.
                                            exists t'.
                                            ltac1:(rewrite lookup_insert).
                                            reflexivity.
                                        }
                                        {
                                            exists phi.
                                            ltac1:(rewrite lookup_insert_ne).
                                            ltac1:(congruence).
                                            ltac1:(rewrite - elem_of_list_to_map).
                                            rewrite NoDup_cons in Hsub_mm'_nodup.
                                            apply Hsub_mm'_nodup.
                                            exact H3.
                                        }
                                    }
                                    exact Hra.
                                }
                                ltac1:(rewrite - Heqm in Hra).
                                ltac1:(rewrite - Heqm in Hra').
                                assert (Hnd1 : (NoDup (fst <$> m))).
                                {
                                    subst m.
                                    apply NoDup_1_renaming_for.
                                }
                                assert(Hynotm : y ∉ (fst <$> m)).
                                {
                                    subst m.
                                    rewrite elem_of_list_fmap.
                                    intros HContra.
                                    destruct HContra as [[z1 z2] [H1 H2]].
                                    simpl in *; subst.
                                    apply Hnt. clear Hnt.
                                    rewrite elem_of_list_fmap.
                                    exists (z1, z2).
                                    simpl.
                                    split>[reflexivity|].
                                    exact H2.
                                }
                                clear Heqm Hnt Hma Hra.
                                revert y m Hnd1 Hynotm Hra'.
                                induction sub_mm'; intros y m Hnd1 Hynotm Hra'.
                                {
                                    simpl. reflexivity.
                                }
                                {
                                    simpl.
                                    destruct a. simpl.
                                    destruct (list_to_map m!!v) eqn:Heq2.
                                    {
                                        destruct (decide (v = y)).
                                        {
                                            subst v.
                                            simpl.
                                            ltac1:(exfalso).
                                            rewrite <- elem_of_list_to_map in Heq2.
                                            apply Hynotm. clear Hynotm.
                                            rewrite elem_of_list_fmap.
                                            exists (y, v0).
                                            simpl.
                                            split>[reflexivity|exact Heq2].
                                            assumption.
                                        }
                                        {
                                            eapply IHsub_mm'.
                                            {
                                                ltac1:(fold (@fmap list list_fmap) in *; idtac).
                                                clear - Hsub_mm'_nodup.
                                                rewrite NoDup_cons in Hsub_mm'_nodup.
                                                simpl in *.
                                                rewrite NoDup_cons in Hsub_mm'_nodup.
                                                rewrite NoDup_cons.
                                                ltac1:(fold (@fmap list list_fmap) in *; idtac).
                                                ltac1:(set_solver).
                                            }
                                            { assumption. }
                                            { assumption. }
                                            {
                                                clear - Hra'.
                                                ltac1:(set_solver).
                                            }
                                        }
                                    }
                                    {
                                        destruct (decide (v = y)).
                                        {
                                            subst v.
                                            ltac1:(exfalso).
                                            clear - Hra' Hynotm.
                                            ltac1:(set_solver).
                                        }
                                        {
                                            eapply IHsub_mm'.
                                            {
                                                ltac1:(fold (@fmap list list_fmap) in *; idtac).
                                                clear - Hsub_mm'_nodup.
                                                rewrite NoDup_cons in Hsub_mm'_nodup.
                                                simpl in *.
                                                rewrite NoDup_cons in Hsub_mm'_nodup.
                                                rewrite NoDup_cons.
                                                ltac1:(fold (@fmap list list_fmap) in *; idtac).
                                                ltac1:(set_solver).
                                            }
                                            { assumption. }
                                            { assumption. }
                                            {
                                                clear - Hra'.
                                                ltac1:(set_solver).
                                            }
                                        }
                                    }
                                }
                                {
                                    fold (@fmap list list_fmap) in *.
                                    apply NoDup_1_renaming_for.
                                }
                            }
                            {
                                fold (@fmap list list_fmap) in *.
                                subst m.
                                rewrite <- IHsub_mm' with (y := y)(x := x).
                                {
                                    apply f_equal2.
                                    {
                                        apply f_equal2.
                                        {
                                            apply functional_extensionality.
                                            intros [v'' t''].
                                            ltac1:(repeat case_match).
                                            {
                                                simpl in *.
                                                ltac1:(rewrite <- elem_of_list_to_map in H).
                                                ltac1:(rewrite <- elem_of_list_to_map in H0).
                                                Check renaming_for.
                                            }
                                        }
                                        {
                                            reflexivity.
                                        }
                                    }
                                    {
                                        reflexivity.
                                    }
                                }
                                clear IHsub_mm'.
                                clear z.
                                eapply IHsub_mm'.
                            }
                        }
                        remember ((list_to_map (renaming_for (<[a.1:=a.2]> ((list_to_map sub_mm')))) !! a.1):(gmap variable (variable))) as Somez.
                        destruct (decide (x0 = x)).
                        {

                        }
                    }





                    Check NoTwice_renaming_for.
                    remember ((elements (dom (list_to_map sub_mm')) ++ elements (⋃ (vars_of <$> sub_mm'.*2)))) as avoid.
                    assert (Havoid: (elements (dom ((list_to_map sub_mm'):(gmap variable (TermOver BuiltinOrVar)))) ++ elements (⋃ (vars_of <$> sub_mm'.*2))) ⊆ avoid) by (ltac1:(set_solver)).
                    clear Heqavoid.
                    ltac1:(rewrite dom_list_to_map_L).
                    (* Search gmap nat. *)
                    (* Check card. *)
                    (* Search elements list_to_set. *)
                    remember ( (length (elements (dom (list_to_map sub_mm'))))) as n.
                    clear Heqn.
                    
                    (* ltac1:(setoid_rewrite -> elements_list_to_set). *)
                    (* Search elements list_to_set. *)
                    (* Search dom list_to_map. *)
                    revert x y n avoid Havoid Hy.
                    induction sub_mm'; intros x y n avoid Havoid Hy; simpl in *.
                    {
                        subst.
                        apply elem_of_list_to_map_2 in Hy.
                        apply elem_of_zip_l in Hy.
                        ltac1:(rewrite dom_empty_L in Hy).
                        rewrite elements_empty in Hy.
                        rewrite elem_of_nil in Hy.
                        destruct Hy.
                    }
                    {
                        ltac1:(repeat case_match; simpl in *; simplify_eq/=).
                        {
                            clear H1.
                            fold (@fmap list list_fmap) in *.
                            Check NoTwice_renaming_for.
                            (* Search dom insert. *)
                            ltac1:(rewrite dom_insert_L).
                            Search list_to_map zip.
                            eapply IHsub_mm'.
                        }
                        {

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
