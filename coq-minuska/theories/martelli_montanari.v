From Minuska Require Import
    prelude
    spec
    unification_interface
    basic_properties
.

From stdpp Require Import
    listset
    relations
.

(* Own Ltac macros *)
Ltac resymde S Name HName :=
  remember S as Name eqn:HName; symmetry in HName; destruct Name
.

(* Unification Problem *)

(* borrowed from textbook_unification_alg.v 
  other functionality, yet not required may be borrowed
  as well; though then maybe consider importing it *)
Definition eqn {Σ : StaticModel} : Type :=
    ((TermOver BuiltinOrVar)*(TermOver BuiltinOrVar))%type
.

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

Definition is_unifier_of {Σ : StaticModel} (s : SubTMM) (l : list eqn) :=
  Forall (fun '(e1, e2) => sub_app_mm s e1 = sub_app_mm s e2) l
.

Definition UP {Σ : StaticModel} : Type := listset eqn.

Definition equiv_UP {Σ : StaticModel} (up up' : UP) : Prop :=
  ∀ s : SubTMM, is_unifier_of s (elements up) <-> is_unifier_of s (elements up')
.

Notation "x ~up y" := (equiv_UP x y) (at level 70).


(* MultiEquation *)

Definition Meqn {Σ : StaticModel} : Type :=
  (gset (variable) * list (TermOver BuiltinOrVar))%type
.

Definition init_meqn {Σ : StaticModel} (s : gset variable) (m : list (TermOver BuiltinOrVar)) : Meqn :=
  (s, m)
.

Definition meqns_s_intersect {Σ : StaticModel} (meqn : Meqn) (meqn' : Meqn) : bool :=
  let '(s, m) := meqn in
  let '(s',m') := meqn' in
    bool_decide (s ∩ s' ≢ ∅)
.

Definition meqn_subst {Σ : StaticModel} (meqn : Meqn) (sub : SubTMM) : Meqn := 
  let '(s, m) := meqn in (s, (sub_app_mm sub) <$> m)
.

Instance ls_to_bor_dec {Σ : StaticModel} : EqDecision (listset (TermOver BuiltinOrVar)).
Proof.
ltac1:(solve_decision).
Defined.

Instance meqn_dec {Σ : StaticModel} : EqDecision Meqn.
Proof.
ltac1:(solve_decision).
Defined.

Instance listset_eqdec {A : Type} {_aed : EqDecision A} : EqDecision (listset A).
Proof.
ltac1:(solve_decision).
Defined.

Definition var_to_term {Σ : StaticModel} (v : variable) : TermOver BuiltinOrVar :=
  t_over (bov_variable v)
.

Definition var_term_to_var {Σ : StaticModel} (tv : TermOver BuiltinOrVar) : option (variable) :=
  match tv with
    | t_over (bov_variable v) => Some v
    | _ => None
  end
.

Lemma var_term_to_var_some {Σ : StaticModel} :
  ∀ (t : TermOver BuiltinOrVar) (v : variable), var_term_to_var t = Some v <-> t = t_over (bov_variable v)
.
Proof.
split.
{
  intros.
  unfold var_term_to_var in H.
  ltac1:(repeat case_match; simplify_eq; reflexivity).
}
{
  intros.
  unfold var_term_to_var.
  rewrite H.
  reflexivity.
}
Qed.

Definition get_var_part {Σ : StaticModel} (meqn : Meqn) : gset variable :=
  fst meqn
.

Definition get_nonvar_part {Σ : StaticModel} (meqn : Meqn) : list (TermOver BuiltinOrVar) :=
  snd meqn
.

Definition meqn_m_empty {Σ : StaticModel} (meqn : Meqn) : bool :=
  match get_nonvar_part meqn with
    | [] => true
    | _ => false
  end
.

Global Instance meqn_empty {Σ : StaticModel} : Empty Meqn :=
  (empty, [])
.

Global Instance meqn_elem_of {Σ : StaticModel} : ElemOf (TermOver BuiltinOrVar) Meqn :=
  λ t meqn,
    match t with
      | t_over (bov_variable v) => v ∈ get_var_part meqn
      | _ => t ∈ get_nonvar_part meqn
    end
.

(* This definition, as is, is needed for set_equiv_instance - used in use of union_list lemmas *)
Global Instance meqn_equiv {Σ : StaticModel} : Equiv Meqn :=
  λ (meqn meqn' : Meqn), ∀ (t : TermOver BuiltinOrVar), t ∈ meqn <-> t ∈ meqn'
.

Lemma meqn_equivalent_refl {Σ : StaticModel} : Reflexive meqn_equiv.
Proof.
unfold Reflexive.
intros.
unfold meqn_equiv.
reflexivity.
Qed.

Lemma meqn_equivalent_symm {Σ : StaticModel} : Symmetric meqn_equiv.
Proof.
unfold Symmetric.
intros.
unfold meqn_equiv in *.
symmetry.
specialize (H t).
assumption.
Qed.

Lemma meqn_equivalent_trans {Σ : StaticModel} : Transitive meqn_equiv.
Proof.
unfold Transitive.
intros.
unfold meqn_equiv in *.
ltac1:(set_solver).
Qed.

Instance meqn_equivalence {Σ : StaticModel} : Equivalence meqn_equiv := {|
  Equivalence_Reflexive := meqn_equivalent_refl;
  Equivalence_Symmetric := meqn_equivalent_symm;
  Equivalence_Transitive := meqn_equivalent_trans;
|}.

Global Instance meqn_union {Σ : StaticModel} : Union Meqn :=
  λ meqn meqn', (meqn.1 ∪ meqn'.1, meqn.2 ++ meqn'.2)
.

Global Instance meqn_singleton {Σ : StaticModel} : Singleton (TermOver BuiltinOrVar) Meqn :=
  λ t, match t with
      | t_over (bov_variable v) => ({[v]}, [])
      | _ => (∅, [t])
    end
.

Lemma not_elem_of_empty_meqn {Σ : StaticModel} :
  ∀ (t : TermOver BuiltinOrVar), t ∉ (∅ : Meqn)
.
Proof.
intros.
unfold empty.
unfold meqn_empty.
unfold elem_of.
unfold meqn_elem_of.
simpl.
unfold not.
intros.
ltac1:(repeat case_match; simplify_eq; try (apply not_elem_of_empty in H; destruct H); try (apply not_elem_of_nil in H; destruct H)).
Qed.

Lemma elem_of_singleton_meqn {Σ : StaticModel} :
  ∀ (x y : TermOver BuiltinOrVar), x ∈ ({[y]} : Meqn) ↔ x = y
.
Proof.
split.
{
  intros.
  unfold singleton in H.
  unfold meqn_singleton in H.
  unfold elem_of in H.
  unfold meqn_elem_of in H.
  unfold get_nonvar_part in H.
  ltac1:(repeat case_match; simplify_eq; simpl in H;
    try (rewrite elem_of_list_singleton in H; assumption);
    try (rewrite elem_of_singleton in H; subst; reflexivity);
    try (apply not_elem_of_nil in H; destruct H);
    try (apply not_elem_of_empty in H; destruct H); repeat (rewrite (elem_of_singleton_1 _ _ H))).
}
{
  intros.
  rewrite H.
  unfold singleton.
  unfold meqn_singleton.
  unfold elem_of.
  unfold meqn_elem_of.
  unfold get_nonvar_part.
  ltac1:(repeat case_match; simpl; try (rewrite elem_of_singleton; reflexivity); try (rewrite elem_of_list_singleton; reflexivity)).
}
Qed.

Lemma elem_of_union_meqn {Σ : StaticModel}:
  ∀ (X Y : Meqn) (x : TermOver BuiltinOrVar), x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
.
Proof.
split.
{
  intros.
  unfold elem_of in *.
  unfold meqn_elem_of in *.
  unfold get_nonvar_part in *.
  unfold get_var_part in *.
  ltac1:(repeat case_match; simpl;
    try (setoid_rewrite elem_of_union in H; assumption);
    try (simpl in H; rewrite elem_of_app in H; assumption)).
}
{
  intros.
  unfold elem_of in *.
  unfold meqn_elem_of in *.
  unfold get_nonvar_part in *.
  unfold get_var_part in *.
  ltac1:(repeat case_match; simpl;
    try (rewrite <- elem_of_union in H; assumption);
    try (rewrite elem_of_app; assumption)).
}
Qed.

Global Instance meqn_semiset {Σ : StaticModel} : SemiSet (TermOver BuiltinOrVar) Meqn := {|
  not_elem_of_empty := not_elem_of_empty_meqn;
  elem_of_singleton := elem_of_singleton_meqn;
  elem_of_union := elem_of_union_meqn;
|}.

Lemma var_elem_of_meqn {Σ : StaticModel} :
  ∀ (meqn : Meqn) (v : variable),
    v ∈ get_var_part meqn <-> var_to_term v ∈ meqn
.
Proof.
split.
{
  intros.
  unfold elem_of.
  unfold meqn_elem_of.
  unfold var_to_term.
  assumption.
}
{
  intros.
  unfold elem_of in H.
  unfold meqn_elem_of in H.
  unfold var_to_term in H.
  assumption.
}
Qed.

Definition term_is_var {Σ : StaticModel} (t : TermOver BuiltinOrVar) : bool :=
  match t with
    | t_over (bov_variable _) => true
    | _ => false
  end
.

Definition term_is_nonvar {Σ : StaticModel} (t : TermOver BuiltinOrVar) : bool := ~~ (term_is_var t).

Definition meqn_right_valid {Σ : StaticModel} (meqn : Meqn) : Prop :=
  ∀ t : TermOver BuiltinOrVar, t ∈ get_nonvar_part meqn -> term_is_nonvar t
.

Definition meqn_left_valid {Σ : StaticModel} (meqn : Meqn) : Prop :=
  ∃ v : variable, v ∈ get_var_part meqn
.

Definition meqn_valid {Σ : StaticModel} (meqn : Meqn) : Prop :=
  meqn_left_valid meqn ∧ meqn_right_valid meqn
.


(* Relations *)


Definition rel_up {Σ : StaticModel} (up : UP) (t t' : TermOver BuiltinOrVar) : Prop :=
  (t, t') ∈ up
.

Definition rel_up_closure {Σ : StaticModel} (up : UP) : relation (TermOver BuiltinOrVar) := 
  rtsc (rel_up up)
.

Definition represents'' {Σ : StaticModel} (meqn : Meqn) (up : UP) : Prop :=
  meqn_valid meqn ->
  ∀ (t t' : TermOver BuiltinOrVar),
  (t ∈ meqn ∧
  t' ∈ meqn) <->
  rel_up_closure up t t'
.

Definition create_eqn {Σ : StaticModel} (t t' : TermOver BuiltinOrVar) : eqn := 
  (t, t')
.

Definition RST_list_closure {A : Type} (la : list A) (lb : list A) : list (A * A)%type :=
  (cprod la la) ++ (cprod lb lb) ++ (cprod la lb) ++ (cprod lb la)
.

Lemma RST_list_closure_elem_of {A : Type} :
  ∀ (la lb : list A) (x y : A),
    (x ∈ la ∨ x ∈ lb) ∧ (y ∈ la ∨ y ∈ lb) <->
    (x, y) ∈ RST_list_closure la lb
.
Proof.
intros la lb x y.
split.
{
  intros [H0 H1].
  unfold RST_list_closure.
  destruct H0 as [H0 | H0].
  {
    destruct H1 as [H1 | H1].
    {
      assert ((x, y) ∈ cprod la la).
      {
        rewrite elem_of_list_cprod.
        simpl.
        split; assumption.
      }
      apply (@or_introl _ ((x, y) ∈ (cprod lb lb ++ cprod la lb ++ cprod lb la))) in H.
      rewrite <- elem_of_app in H.
      assumption.
    }
    {
      assert ((x, y) ∈ cprod la lb).
      {
        rewrite elem_of_list_cprod.
        simpl.
        split; assumption.
      }
      apply (@or_introl _ ((x, y) ∈ (cprod lb la))) in H.
      rewrite <- elem_of_app in H.
      apply (@or_intror ((x, y) ∈ (cprod la la ++ cprod lb lb))) in H.
      rewrite <- elem_of_app in H.
      rewrite <- app_assoc in H.
      assumption.
    }
  }
  {
    destruct H1 as [H1 | H1].
    {
      assert ((x, y) ∈ cprod lb la).
      {
        rewrite elem_of_list_cprod.
        simpl.
        split; assumption.
      }
      rewrite elem_of_app.
      right.
      rewrite elem_of_app.
      right.
      rewrite elem_of_app.
      right.
      assumption.
    }
    {
      assert ((x, y) ∈ cprod lb lb).
      {
        rewrite elem_of_list_cprod.
        simpl.
        split; assumption.
      }
      rewrite elem_of_app.
      right.
      rewrite elem_of_app.
      left.
      assumption.
    }
  }
}
{
  intros.
  unfold RST_list_closure in H.
  repeat (rewrite elem_of_app in H).
  repeat (rewrite elem_of_list_cprod in H).
  ltac1:(set_solver).
}
Qed.

Lemma meqn_valid_elem_of_in {Σ : StaticModel} :
  ∀ (meqn : Meqn), meqn_valid meqn ->
    ∀ (t : TermOver BuiltinOrVar), t ∈ meqn <-> (∃ (v : variable), var_term_to_var t = Some v ∧ v ∈ get_var_part meqn) ∨ (t ∈ get_nonvar_part meqn)
.
Proof.
intros meqn HI1.
split.
{
  intros.
  unfold elem_of in H.
  unfold meqn_elem_of in H.
  ltac1:(repeat case_match; simplify_eq).
 {
  right.
  assumption.
 }
 {
  left.
  exists x.
  simpl.
  split.
   {
  reflexivity.
   }
   {
  assumption.
   }
 }
 {
  right.
  assumption.
 }
}
{
  intros.
  destruct H.
 {
  destruct H as [v [H H']].
  unfold elem_of.
  unfold meqn_elem_of.
  apply var_term_to_var_some in H.
  rewrite H.
  assumption.
 }
 {
  unfold elem_of.
  unfold meqn_elem_of.
  ltac1:(repeat case_match; simplify_eq).
   {
    assumption.
   }
   {
    unfold meqn_valid in HI1.
    destruct HI1 as [_ HI1].
    unfold meqn_right_valid in HI1.
    specialize (HI1 (t_over (bov_variable x)) H).
    unfold term_is_nonvar in HI1.
    unfold term_is_var in HI1.
    simpl in HI1.
    inversion HI1.
   }
   {
    assumption.
   }
 }
}
Qed.

Definition up_of_meqn {Σ : StaticModel} (meqn : Meqn) : UP :=
  let '(var_part, nonvar_part) := meqn in
    list_to_set (RST_list_closure (var_to_term <$> elements var_part) nonvar_part)
.

Lemma up_of_meqn_elem_of {Σ : StaticModel} :
  ∀ (meqn : Meqn), meqn_valid meqn -> ∀ (t t' : TermOver BuiltinOrVar), t ∈ meqn ∧ t' ∈ meqn <-> (t, t') ∈ up_of_meqn meqn
.
Proof.
intros.
split.
{
  intros [H0 H1].
  rewrite (meqn_valid_elem_of_in meqn H _) in H0.
  rewrite (meqn_valid_elem_of_in meqn H _) in H1.
  destruct H0.
  {
    destruct H0 as [v [H0 H0']].
    destruct H1.
    {
      destruct H1 as [v' [H1 H1']].
      unfold up_of_meqn.
      destruct meqn.
      rewrite elem_of_list_to_set.
      rewrite <- RST_list_closure_elem_of.
      split.
      {
        left.
        unfold get_var_part in H0'.
        simpl in H0'.
        rewrite elem_of_list_fmap.
        exists v.
        split.
        {
          apply var_term_to_var_some in H0.
          unfold var_to_term.
          assumption.
        }
        {
          rewrite elem_of_elements.
          assumption.
        }
      }
      {
        left.
        unfold get_var_part in H1'.
        simpl in H1'.
        rewrite elem_of_list_fmap.
        exists v'.
        split.
        {
          apply var_term_to_var_some in H1.
          unfold var_to_term.
          assumption.
        }
        {
          rewrite elem_of_elements.
          assumption.
        }
      }
    }
    {
      unfold up_of_meqn.
      destruct meqn.
      rewrite elem_of_list_to_set.
      rewrite <- RST_list_closure_elem_of.
      split.
      {
        left.
        rewrite elem_of_list_fmap.
        exists v.
        split.
        {
          apply var_term_to_var_some in H0.
          unfold var_to_term.
          assumption.
        }
        {
          rewrite elem_of_elements.
          assumption.
        }
      }
      {
        right.
        unfold get_nonvar_part in H1.
        simpl in H1.
        assumption.
      }
    }
  }
  {
    destruct H1 as [[v' [H1 H1']] | H1].
    {
      unfold up_of_meqn.
      destruct meqn.
      rewrite elem_of_list_to_set.
      rewrite <- RST_list_closure_elem_of.
      split.
      {
        right.
        unfold get_nonvar_part in H0.
        simpl in H0.
        assumption.
      }
      {
        left.
        rewrite elem_of_list_fmap.
        exists v'.
        split.
        {
          apply var_term_to_var_some in H1.
          unfold var_to_term.
          assumption.
        }
        {
          unfold get_var_part in H1'.
          simpl in H1'.
          rewrite elem_of_elements.
          assumption.
        }
      }
    }
    {
      unfold up_of_meqn.
      destruct meqn.
      rewrite elem_of_list_to_set.
      rewrite <- RST_list_closure_elem_of.
      split.
      {
        right.
        unfold get_nonvar_part in H0.
        assumption.
      }
      {
        right.
        unfold get_nonvar_part in H1.
        assumption.
      }
    }
  }
}
{
  intros.
  unfold up_of_meqn in H0.
  do 2 (rewrite (meqn_valid_elem_of_in _ H)).
  destruct meqn.
  rewrite elem_of_list_to_set in H0.
  rewrite <- RST_list_closure_elem_of in H0.
  do 2 (rewrite elem_of_list_fmap in H0).
  unfold get_nonvar_part.
  simpl.
  setoid_rewrite <- elem_of_elements.
  setoid_rewrite var_term_to_var_some.
  unfold var_to_term in H0.
  assumption.
}
Qed.

(* Representation *)

Definition get_vars_of_var_part_list_meqns {Σ : StaticModel} (car : list Meqn) : gset variable :=
  list_to_set (concat ((elements ∘ get_var_part) <$> car))
.

Lemma get_vars_of_var_part_list_meqns_equiv {Σ : StaticModel} :
  ∀ (lm : list Meqn) (v : variable),
    v ∈ get_vars_of_var_part_list_meqns lm <-> Exists (fun x => v ∈ get_var_part x) lm
.
Proof.
split.
{
  intros.
  rewrite Exists_exists.
  unfold get_vars_of_var_part_list_meqns in H.
  rewrite elem_of_list_to_set in H.
  rewrite elem_of_list_In in H.
  rewrite in_concat in H.
  destruct H as [lv [H0 H1]].
  rewrite <- elem_of_list_In in H0.
  rewrite <- elem_of_list_In in H1.
  rewrite list_fmap_compose in H0.
  rewrite elem_of_list_fmap in H0.
  destruct H0 as [lsv [H0 H2]].
  rewrite elem_of_list_fmap in H2.
  destruct H2 as [meqn [H2 H3]].
  rewrite H0 in H1.
  rewrite elem_of_elements in H1.
  rewrite H2 in H1.
  exists meqn.
  ltac1:(pose proof (conj H3 H1)).
  assumption.
}
{
  intros.
  rewrite Exists_exists in H.
  destruct H as [meqn [H0 H1]].
  unfold get_vars_of_var_part_list_meqns.
  rewrite elem_of_list_to_set.
  rewrite elem_of_list_In.
  rewrite in_concat.
  remember (concat (elements ∘ get_var_part <$> lm)) as lv.
  ltac1:(pose proof (elem_of_list_fmap_1 get_var_part lm meqn H0)).
  remember (get_var_part meqn) as ls_v_meqn.
  remember (get_var_part <$> lm) as gvp_lm.
  ltac1:(pose proof (elem_of_list_fmap_1 elements gvp_lm ls_v_meqn H)).
  rewrite <- elem_of_elements in H1.
  exists (elements ls_v_meqn).
  do 2 (rewrite <- elem_of_list_In).
  rewrite Heqgvp_lm in H2.
  rewrite list_fmap_compose.
  ltac1:(pose proof (conj)).
  specialize (H3 (elements ls_v_meqn ∈ elements <$> (get_var_part <$> lm)) (v ∈ elements ls_v_meqn) H2 H1).
  assumption.
}
Qed.

Definition get_vars_of_nonvar_part_list_meqns {Σ : StaticModel} (car : list Meqn) : gset variable :=
  let terms_sets : list (list (TermOver BuiltinOrVar)) := get_nonvar_part <$> car in
  let terms : list (TermOver BuiltinOrVar) := concat terms_sets in
  let vars : list (gset variable) := vars_of <$> terms in
    ⋃ vars
.

Definition get_vars_of_var_part_listset_meqns {Σ : StaticModel} (car : listset Meqn) : gset variable :=
  get_vars_of_var_part_list_meqns (elements car)
.

Lemma get_vars_of_var_part_listset_meqns_equiv {Σ : StaticModel} :
  ∀ (ls : listset Meqn) (v : variable),
    v ∈ get_vars_of_var_part_listset_meqns ls <-> (∃ (meqn : Meqn), meqn ∈ ls ∧ v ∈ get_var_part meqn )
.
Proof.
intros.
unfold get_vars_of_var_part_listset_meqns.
ltac1:(pose proof((get_vars_of_var_part_list_meqns_equiv (elements ls) v))).
rewrite Exists_exists in H.
setoid_rewrite elem_of_elements in H.
assumption.
Qed.

Definition get_vars_of_nonvar_part_listset_meqns {Σ : StaticModel} (car : listset Meqn) : gset variable :=
  get_vars_of_nonvar_part_list_meqns (elements car)
.

(* DEC PART *)

Definition term_is_constant {Σ : StaticModel} (t : TermOver BuiltinOrVar) : bool :=
  match t with
    | t_over _ => true
    | _ => false
  end
.

Definition term_params {Σ : StaticModel} (t : TermOver BuiltinOrVar) : option (list (TermOver BuiltinOrVar)) :=
  match t with
    | t_term _ l => Some l
    | _ => None
  end
.


Class U_ops
  {Σ : StaticModel}
:= {
    U : Type;

    U_empty :: Empty U;
    U_elements :: Elements Meqn U;

    U_NoDup :
      ∀ (u : U), NoDup (elements u)
    ;

    u_map :
      U -> (Meqn -> Meqn) -> U
    ;

    u_insert :
      U -> Meqn -> U
    ;

    u_insert_id :
      ∀ (u : U) (meqn : Meqn), meqn ∈ elements u -> elements (u_insert u meqn) ≡ₚ elements u
    ;

    u_insert_add :
      ∀ (u : U) (meqn : Meqn), meqn ∉ elements u -> elements (u_insert u meqn) ≡ₚ meqn :: elements u
    ;

    u_extract_nonempty_m_meqn :
        U -> option (Meqn * U)%type
    ;

    u_extract_nonempty_m_removes_element :
      ∀ (u u' : U) (meqn : Meqn), u_extract_nonempty_m_meqn u = Some (meqn, u') -> meqn ∉ elements u'
    ;

    u_extract_nonempty_m_insert_equiv :
      ∀ (u u' : U) (meqn : Meqn), u_extract_nonempty_m_meqn u = Some (meqn, u') -> meqn :: elements u' ≡ₚ elements u
    ;

    u_extract_nonempty_m_meqn_is_nonempty :
      ∀ (u u' : U) (meqn : Meqn), u_extract_nonempty_m_meqn u = Some (meqn, u') -> ~~ meqn_m_empty meqn
    ;

    u_extract_overlapping_meqns :
      U -> variable -> (listset Meqn * U)%type
    ;

    u_extract_overlapping_meqns_in_ls_meqn :
      ∀ (u u' : U) (v : variable) (ls_meqn : listset Meqn) (meqn : Meqn),
        u_extract_overlapping_meqns u v = (ls_meqn, u') ->
        meqn ∈ elements u ->
        (meqn ∈ ls_meqn <-> v ∈ get_var_part meqn)
    ;

    u_extract_overlapping_meqns_in_u' :
      ∀ (u u' : U) (v : variable) (ls_meqn : listset Meqn) (meqn : Meqn),
        u_extract_overlapping_meqns u v = (ls_meqn, u') ->
        meqn ∈ elements u ->
        (meqn ∈ elements u' <-> v ∉ get_var_part meqn)
    ;
    u_extract_overlapping_meqns_insert_equiv :
      ∀ (u u' : U) (v : variable) (ls_meqn : listset Meqn),
        u_extract_overlapping_meqns u v = (ls_meqn, u') ->
        elements u ≡ₚ elements ls_meqn ++ elements u'
    ;
}.

Definition u_valid {Σ : StaticModel} {u_ops : U_ops} (u : U) : Prop :=
  Forall (fun meqn => meqn_valid meqn) (elements u)
.


Definition up_of_list {Σ : StaticModel} (lm : list Meqn) : UP :=
  ⋃ (up_of_meqn <$> lm)
.

Lemma up_of_list_all_terms_in_UP {Σ : StaticModel} :
  ∀ (lm : list Meqn), Forall (fun meqn => meqn_valid meqn) lm ->
  Forall (fun meqn => ∀ (t t' : TermOver BuiltinOrVar), t ∈ meqn ∧ t' ∈ meqn -> (t, t') ∈ up_of_list lm) lm
.
Proof.
intros.
rewrite Forall_forall.
intros.
unfold up_of_list.
rewrite elem_of_union_list.
exists (up_of_meqn x).
split.
{
  apply elem_of_list_fmap_1.
  assumption.
}
{
  rewrite Forall_forall in H.
  specialize (H x H0).
  rewrite (up_of_meqn_elem_of _ H _ _) in H1.
  assumption.
}
Qed.

Lemma up_of_list_elem_of {Σ : StaticModel} :
  ∀ (lm : list Meqn) (t t' : TermOver BuiltinOrVar), Forall (fun meqn => meqn_valid meqn) lm -> 
    (t, t') ∈ up_of_list lm <-> Exists (fun meqn => t ∈ meqn ∧ t' ∈ meqn) lm
.
Proof.
intros.
split.
{
  intros.
  unfold up_of_list in H0.
  rewrite elem_of_union_list in H0.
  destruct H0 as [up [H0 H1]].
  rewrite elem_of_list_fmap in H0.
  destruct H0 as [meqn [H0 H0']].
  rewrite Exists_exists.
  exists meqn.
  split.
  {
    assumption.
  }
  {
    rewrite H0 in H1.
    rewrite Forall_forall in H.
    specialize (H meqn H0').
    rewrite <- (up_of_meqn_elem_of _ H) in H1.
    assumption.
  }
}
{
  rewrite Exists_exists.
  intros.
  destruct H0 as [meqn [H0 H1]].
  unfold up_of_list.
  rewrite elem_of_union_list.
  unfold u_valid in H.
  rewrite Forall_forall in H.
  specialize (H meqn H0).
  rewrite (up_of_meqn_elem_of _ H) in H1.
  exists (up_of_meqn meqn).
  split.
  {
    apply elem_of_list_fmap_1.
    assumption.
  }
  {
    assumption.
  }
}
Qed.

Definition up_of_u {Σ : StaticModel} {u_ops : U_ops} (u : U) : UP :=
  up_of_list (elements u)
.

Lemma up_of_valid_u_meqn_all_terms_in_UP {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u : U), u_valid u ->
    Forall (fun meqn => ∀ (t t' : TermOver BuiltinOrVar), t ∈ meqn ∧ t' ∈ meqn -> (t, t') ∈ up_of_u u) (elements u)
.
Proof.
intros.
unfold u_valid in H.
apply (up_of_list_all_terms_in_UP _ H).
Qed.

Lemma up_of_valid_u_elem_of {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u : U) (t t' : TermOver BuiltinOrVar), u_valid u -> 
    (t, t') ∈ up_of_u u <-> Exists (fun meqn => t ∈ meqn ∧ t' ∈ meqn) (elements u)
.
Proof.
intros.
unfold u_valid in H.
apply (up_of_list_elem_of _ t t' H).
Qed.

Definition u_get_vars {Σ : StaticModel} {u_ops : U_ops} (u : U) : gset variable := 
  ⋃ (get_var_part <$> (elements u))
.

Lemma u_extract_overlapping_meqns_disjunct {Σ : StaticModel} {u_ops : U_ops}:
  ∀ (u u' : U) (v : variable) (ls_meqn : listset Meqn) (meqn : Meqn),
    u_extract_overlapping_meqns u v = (ls_meqn, u') ->
    meqn ∈ elements u <->
    meqn ∈ ls_meqn ∨ meqn ∈ elements u'
.
Proof.
intros.
split.
{
  intros.
  ltac1:(pose proof (u_extract_overlapping_meqns_in_ls_meqn u u' v ls_meqn meqn H H0)).
  ltac1:(pose proof (u_extract_overlapping_meqns_in_u' u u' v ls_meqn meqn H H0)).
  destruct (decide(v ∈ get_var_part meqn)) as [H3 | H3].
  {
    rewrite <- H1 in H3.
    left.
    assumption.
  }
  {
    rewrite <- H2 in H3.
    right.
    assumption.
  }
}
{
  intros.
  ltac1:(pose proof (u_extract_overlapping_meqns_insert_equiv u u' v ls_meqn H)).
  rewrite H1.
  rewrite elem_of_app.
  rewrite <- elem_of_elements in H0.
  assumption.
}
Qed.

Lemma u_get_vars_exists_meqn {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u : U) (v : variable),
    v ∈ u_get_vars u <-> Exists (fun meqn => v ∈ get_var_part meqn) (elements u)
.
Proof.
setoid_rewrite Exists_exists.
split.
{
  intros.
  unfold u_get_vars in H.
  rewrite (elem_of_union_list (get_var_part <$> elements u) v) in H.
  destruct H as [gv [H0 H1]].
  rewrite elem_of_list_fmap in H0.
  destruct H0 as [meqn [H0 H2]].
  subst.
  exists meqn.
  apply (conj H2 H1).
}
{
  intros.
  destruct H as [meqn [H0 H1]].
  unfold u_get_vars.
  rewrite (elem_of_union_list (get_var_part <$> elements u) v).
  exists (get_var_part meqn).
  rewrite elem_of_list_fmap.
  split.
  {
    exists meqn.
    assert (get_var_part meqn = get_var_part meqn) by reflexivity.
    apply (conj H H0).
  }
  {
    assumption.
  }
}
Qed.

Lemma u_insert_elem_of {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (meqn : Meqn),
    u_insert u meqn = u' -> ∀ meqn', meqn' ∈ elements u' <-> meqn' ∈ elements u \/ (meqn' = meqn ∧ meqn ∉ elements u)
.
Proof.
split.
{
  intros.
  destruct (decide (meqn ∈ elements u)) as [H1 | H1].
  {
    left.
    apply u_insert_id in H1.
    rewrite H in H1.
    rewrite <- H1.
    assumption.
  }
  {
    ltac1:(pose proof H0).
    ltac1:(pose proof H1).
    apply u_insert_add in H1.
    rewrite H in H1.
    rewrite H1 in H0.
    rewrite elem_of_cons in H0.
    destruct H0.
    {
      right.
      apply (conj H0 H3).
    }
    {
      left.
      assumption.
    }
  }
}
{
  intros.
  destruct H0.
  {
    destruct (decide (meqn ∈ elements u)) as [H1 | H1].
    {
      apply u_insert_id in H1.
      rewrite H in H1.
      rewrite H1.
      assumption.
    }
    {
      apply u_insert_add in H1.
      rewrite H in H1.
      rewrite H1.
      rewrite elem_of_cons.
      right.
      assumption.
    }
  }
  {
    destruct H0 as [H0 H1].
    apply u_insert_add in H1.
    rewrite H in H1.
    rewrite H1.
    rewrite H0.
    apply elem_of_list_here.
  }
}
Qed.

Lemma u_insert_keeps_u_get_vars_lf {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (meqn : Meqn),
    elements (u_insert u meqn) ≡ₚ elements u' ->
    ∀ (v : variable), v ∈ u_get_vars u' -> v ∈ u_get_vars u ∨ v ∈ get_var_part meqn
.
Proof.
intros.
destruct (decide (v ∈ u_get_vars u)) as [H1 | H1].
{
  left.
  assumption.
}
{
  destruct (decide (v ∈ get_var_part meqn)) as [H2 | H2].
  {
    right.
    assumption.
  }
  {
    ltac1:(exfalso).
    rewrite u_get_vars_exists_meqn in H0.
    rewrite Exists_exists in H0.
    destruct H0 as [meqn' [H3 H4]].
    destruct (decide (meqn ∈ elements u)) as [H5 | H5].
    {
      ltac1:(pose proof (u_insert_id _ _ H5)).
      rewrite H0 in H.
      rewrite <- H in H3.
      assert (Exists (fun meqn => v ∈ get_var_part meqn) (elements u)).
      {
        rewrite Exists_exists.
        exists meqn'.
        apply (conj H3 H4).
      }
      rewrite <- u_get_vars_exists_meqn in H6.
      apply H1 in H6.
      destruct H6.
    }
    {
      ltac1:(pose proof (u_insert_add _ _ H5)).
      rewrite H0 in H.
      rewrite <- H in H3.
      rewrite elem_of_cons in H3.
      destruct H3.
      {
        rewrite H3 in H4.
        apply H2 in H4.
        destruct H4.
      }
      {
        assert (Exists (fun meqn => v ∈ get_var_part meqn) (elements u)).
        {
          rewrite Exists_exists.
          exists meqn'.
          apply (conj H3 H4).
        }
        rewrite <- u_get_vars_exists_meqn in H6.
        apply H1 in H6.
        destruct H6.
      }
    }
  }
}
Qed.

Lemma u_insert_keeps_u_get_vars_rg {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (meqn : Meqn),
    elements (u_insert u meqn) ≡ₚ elements u' ->
    ∀ (v : variable), v ∈ u_get_vars u ∨ v ∈ get_var_part meqn -> v ∈ u_get_vars u'
.
Proof.
intros.
destruct H0.
{
  destruct (decide (meqn ∈ elements u)) as [H1 | H1].
  {
    ltac1:(pose proof (u_insert_id _ _ H1)).
    rewrite H2 in H.
    rewrite u_get_vars_exists_meqn in *.
    rewrite Exists_exists in *.
    destruct H0 as [meqn' [H0 H4]].
    exists meqn'.
    rewrite H in H0.
    apply (conj H0 H4).
  }
  {
    ltac1:(pose proof (u_insert_add _ _ H1)).
    rewrite H2 in H.
    rewrite u_get_vars_exists_meqn in *.
    rewrite Exists_exists in *.
    destruct H0 as [meqn' [H0 H4]].
    exists meqn'.
    apply elem_of_list_further with (y := meqn) in H0.
    rewrite H in H0.
    apply (conj H0 H4).
  }
}
{
  destruct (decide (meqn ∈ elements u)) as [H1 | H1].
  {
    ltac1:(pose proof (u_insert_id _ _ H1)).
    rewrite H2 in H.
    rewrite H in H1.
    rewrite u_get_vars_exists_meqn.
    rewrite Exists_exists.
    exists meqn.
    apply (conj H1 H0).
  }
  {
    ltac1:(pose proof (u_insert_add _ _ H1)).
    rewrite H2 in H.
    rewrite u_get_vars_exists_meqn.
    rewrite Exists_exists.
    exists meqn.
    symmetry in H.
    ltac1:(pose proof (elem_of_Permutation (elements u') meqn)).
    destruct H3 as [_ H3].
    ltac1:(ospecialize (H3 _)).
    {
      exists (elements u).
      assumption.
    }
    apply (conj H3 H0).
  }
}
Qed.

Lemma u_insert_keeps_u_get_vars {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (meqn : Meqn),
    elements (u_insert u meqn) ≡ₚ elements u' ->
    ∀ (v : variable), v ∈ u_get_vars u' <-> v ∈ u_get_vars u ∨ v ∈ get_var_part meqn
.
Proof.
split.
{
revert u u' meqn H v.
exact u_insert_keeps_u_get_vars_lf.
}
{
revert u u' meqn H v.
exact u_insert_keeps_u_get_vars_rg.
}
Qed.

Lemma u_extract_overlapping_meqns_keeps_get_vars {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (v v': variable) (ls_meqn : listset Meqn),
    u_extract_overlapping_meqns u v = (ls_meqn, u') ->
    v' ∈ u_get_vars u <-> v' ∈ u_get_vars u' ∨ v' ∈ get_vars_of_var_part_listset_meqns ls_meqn
.
Proof.
intros.
split.
{
  intros.
  rewrite u_get_vars_exists_meqn in H0.
  rewrite Exists_exists in H0.
  destruct H0 as [meqn [H0 H1]].
  destruct (decide(v ∈ get_var_part meqn)) as [H2 | H2].
  {
    right.
    rewrite <- (u_extract_overlapping_meqns_in_ls_meqn u u' v ls_meqn meqn H H0) in H2.
    apply (get_vars_of_var_part_listset_meqns_equiv ls_meqn v').
    exists meqn.
    ltac1:(pose proof (conj H2 H1)).
    assumption.
  }
  {
    left.
    rewrite <- (u_extract_overlapping_meqns_in_u' u u' v ls_meqn meqn H H0) in H2.
    rewrite u_get_vars_exists_meqn.
    rewrite Exists_exists.
    ltac1:(pose proof (conj H2 H1)).
    exists meqn.
    assumption.
  }
}
{
  intros.
  destruct H0.
  {
    rewrite u_get_vars_exists_meqn in H0.
    rewrite Exists_exists in H0.
    destruct H0 as [meqn [H0 H1]].
    ltac1:(pose proof (or_intror (meqn ∈ ls_meqn) H0)).
    rewrite <- (u_extract_overlapping_meqns_disjunct u u' v ls_meqn meqn H) in H2.
    rewrite u_get_vars_exists_meqn.
    rewrite Exists_exists.
    exists meqn.
    apply (conj H2 H1).
  }
  {
    rewrite (get_vars_of_var_part_listset_meqns_equiv ls_meqn v') in H0.
    destruct H0 as [meqn [H0 H1]].
    ltac1:(pose proof (or_introl (meqn ∈ elements u') H0)).
    rewrite <- (u_extract_overlapping_meqns_disjunct u u' v ls_meqn meqn H) in H2.
    rewrite u_get_vars_exists_meqn.
    rewrite Exists_exists.
    exists meqn.
    apply (conj H2 H1).
  }
}
Qed.

Definition u_insert_listset {Σ : StaticModel} (u to_add : listset Meqn) : listset Meqn := u ∪ to_add.

Definition u_extract_nonempty_m_meqn_listset {Σ : StaticModel} (u : listset Meqn) : option (Meqn * listset Meqn)%type :=
  let '(m_empty, m_nonempty) := partition meqn_m_empty (elements u) in
    match m_nonempty with
      | [] => None
      | x :: xs => Some (x, u ∖ {[x]})
    end
.

Lemma U_NoDup_listset {Σ : StaticModel} : 
  ∀ (ls : listset Meqn), NoDup (elements ls)
.
Proof.
intros.
apply NoDup_elements.
Qed.

Lemma u_extract_nonempty_m_removes_element_listset {Σ : StaticModel}:
  ∀ (u u' : listset Meqn) (meqn : Meqn), u_extract_nonempty_m_meqn_listset u = Some (meqn, u') -> meqn ∉ elements u'
.
Proof.
intros.
unfold u_extract_nonempty_m_meqn_listset in H.
destruct (partition meqn_m_empty (elements u)).
destruct l0.
{
  discriminate.
}
{
  inversion H.
  rewrite elem_of_elements.
  rewrite not_elem_of_difference.
  right.
  rewrite elem_of_singleton.
  reflexivity.
}
Qed.

Lemma u_extract_nonempty_m_insert_equiv_listset {Σ : StaticModel} :
    ∀ (u u' : listset Meqn) (meqn : Meqn),
      u_extract_nonempty_m_meqn_listset u = Some (meqn, u') -> meqn :: elements u' ≡ₚ elements u
.
Proof.
intros.
ltac1:(pose proof (u_extract_nonempty_m_removes_element_listset _ _ _ H)).
unfold u_extract_nonempty_m_meqn_listset in H.
assert (meqn ∈ u).
{
  ltac1:(resymde (partition meqn_m_empty (elements u)) P HeqP).
  destruct l0.
  {
    discriminate.
  }
  {
    inversion H.
    assert (In m (m :: l0)) by (apply in_eq).
    ltac1:(pose proof (@or_intror (In m l) (In m (m :: l0)) H1)).
    rewrite <- (elements_in_partition _ _ HeqP) in H4.
    rewrite <- elem_of_list_In in H4.
    rewrite H2 in H4.
    apply elem_of_elements in H4.
    assumption.
  }
}
destruct (partition meqn_m_empty (elements u)) eqn:P.
destruct l0.
{
  discriminate.
}
{
  inversion H.
  clear H.
  symmetry.
  ltac1:(pose proof (U_NoDup_listset u)).
  apply NoDup_Permutation.
  {
    assumption.
  }
  {
    ltac1:(pose proof (U_NoDup_listset u')).
    rewrite H4.
    apply NoDup_cons_2.
    {
      apply H0.
    }
    {
      assumption.
    }
  }
  split.
  {
    intros.
    rewrite elem_of_cons.
    destruct (decide (x = meqn)).
    {
      left.
      assumption.
    }
    {
      right.
      rewrite elem_of_elements.
      rewrite elem_of_difference.
      split.
      {
        rewrite elem_of_elements in H2.
        assumption.
      }
      rewrite elem_of_singleton.
      assumption.
    }
  }
  {
    intros.
    destruct (decide (x = meqn)).
    {
      rewrite <- e in H1.
      rewrite elem_of_elements.
      assumption.
    }
    {
      rewrite elem_of_cons in H2.
      destruct H2 as [H2 | H2].
      {
        apply n in H2.
        inversion H2.
      }
      {
        rewrite elem_of_elements in H2.
        rewrite elem_of_difference in H2.
        destruct H2 as [H2 _].
        rewrite elem_of_elements.
        assumption.
      }
    }
  }
}
Qed.


Definition u_extract_overlapping_meqns_listset {Σ : StaticModel} (u : listset Meqn) (v : variable)
  : (listset Meqn * listset Meqn)
:=
  let '(t, f) := partition (λ x : Meqn, bool_decide (v ∈ (get_var_part x))) (elements u) in (list_to_set t, list_to_set f)
.

Lemma partition_true_in_tl {A : Type} {_a_eqd : EqDecision A }:
  ∀ (l tl fl : list A) (f : A -> bool) (el : A),
  partition f l = (tl, fl) ->
  el ∈ l ->
  f el = true -> el ∈ tl
.
Proof.
intros l.
induction l.
{
  intros.
  apply not_elem_of_nil in H0.
  destruct H0.
}
{
  intros.
  simpl in *.
  rewrite elem_of_cons in H0.
  destruct H0.
  {
    subst.
    rewrite H1 in H.
    remember (partition f l).
    destruct p.
    inversion H.
    subst.
    clear H.
    rewrite elem_of_cons.
    left.
    reflexivity.
  }
  {
    remember (partition f l).
    destruct p.
    symmetry in Heqp.
    destruct (f a).
    {
      inversion H.
      subst.
      clear H.
      specialize (IHl l0 fl f el Heqp H0 H1).
      rewrite elem_of_cons.
      right.
      assumption.
    }
    {
      inversion H.
      subst.
      clear H.
      eauto.
    }
  }
}
Qed.

Lemma partition_tl_means_true {A : Type} {_a_eqd : EqDecision A }:
  ∀ (l tl fl : list A) (f : A -> bool) (el : A),
  partition f l = (tl, fl) ->
  el ∈ l ->
  el ∈ tl ->
  f el = true
.
Proof.
intros l.
induction l.
{
  intros.
  subst.
  apply not_elem_of_nil in H0.
  destruct H0.
}
{
  intros.
  simpl in *.
  rewrite elem_of_cons in H0.
  destruct H0.
  {
    subst.
    remember (partition f l) as p.
    destruct p.
    remember (f a) as f'.
    destruct f'.
    {
      reflexivity.
    }
    {
      inversion H.
      subst.
      clear H.
      symmetry in Heqp.
      ltac1:(pose proof (elements_in_partition _ _ Heqp a)).
      do 3 (rewrite <- elem_of_list_In in H).
      ltac1:(pose proof (H1) as H1').
      destruct H as [_ H].
      ltac1:(pose proof(or_introl)).
      apply H0 with (B := (a ∈ l1)) in H1.
      apply H in H1.
      clear H.
      clear H0.
      ltac1:(specialize (IHl tl l1 f a Heqp H1 H1')).
      rewrite IHl in Heqf'.
      discriminate.
    }
  }
  {
    remember (partition f l).
    destruct p.
    remember (f el) as fel'.
    destruct (fel').
    {
      reflexivity.
    }
    {
      symmetry in Heqp.
      remember (f a) as fa'.
      destruct (fa').
      {
        inversion H.
        subst.
        clear H.
        rewrite elem_of_cons in H1.
        destruct H1.
        {
          subst.
          rewrite <- Heqfa' in Heqfel'.
          discriminate.
        }
        {
          specialize (IHl l0 fl f el Heqp H0 H).
          rewrite IHl in Heqfel'.
          discriminate.
        }
      }
      {
        inversion H.
        subst.
        clear H.
        ltac1:(specialize (IHl tl l1 f el Heqp H0 H1)).
        rewrite IHl in Heqfel'.
        discriminate.
      }
    }
  }
}
Qed.

Lemma partition_fl_means_false {A : Type} {_a_eqd : EqDecision A }:
  ∀ (l tl fl : list A) (f : A -> bool) (el : A),
  partition f l = (tl, fl) ->
  el ∈ l ->
  el ∈ fl ->
  f el = false
.
Proof.
intros l.
induction l.
{
  intros.
  subst.
  apply not_elem_of_nil in H0.
  destruct H0.
}
{
  intros.
  simpl in *.
  rewrite elem_of_cons in H0.
  destruct H0.
  {
    subst.
    remember (partition f l) as p.
    destruct p.
    remember (f a) as f'.
    destruct f'.
    {
      inversion H.
      subst.
      clear H.
      symmetry in Heqp.
      ltac1:(pose proof (elements_in_partition _ _ Heqp a)).
      do 3 (rewrite <- elem_of_list_In in H).
      ltac1:(pose proof (H1) as H1').
      destruct H as [_ H].
      ltac1:(pose proof(or_intror)).
      apply H0 with (A := (a ∈ l0)) in H1.
      apply H in H1.
      clear H.
      clear H0.
      ltac1:(specialize (IHl l0 fl f a Heqp H1 H1')).
      rewrite IHl in Heqf'.
      discriminate.
    }
    {
      reflexivity.
    }
  }
  {
    remember (partition f l).
    destruct p.
    remember (f el) as fel'.
    destruct (fel').
    {
      symmetry in Heqp.
      remember (f a) as fa'.
      destruct (fa').
      {
        inversion H.
        subst.
        clear H.
        ltac1:(specialize (IHl l0 fl f el Heqp H0 H1)).
        rewrite IHl in Heqfel'.
        discriminate.
      }
      {
        inversion H.
        subst.
        clear H.
        rewrite elem_of_cons in H1.
        destruct H1.
        {
          subst.
          rewrite <- Heqfa' in Heqfel'.
          discriminate.
        }
        {
          ltac1:(specialize (IHl tl l1 f el Heqp H0 H)).
          rewrite IHl in Heqfel'.
          discriminate.
        }
      }
    }
    {
      reflexivity.
    }
  }
}
Qed.


Lemma partition_tl_fl_disjunct {A : Type} {_a_eqd : EqDecision A }:
  ∀ (l tl fl : list A) (f : A -> bool) (el : A),
  partition f l = (tl, fl) ->
  el ∈ l ->
  el ∉ tl ∨ el ∉ fl
.
Proof.
intros.
ltac1:(assert (¬ (el ∈ tl ∧ el ∈ fl))).
{
  unfold not.
  intros.
  destruct H1.
  ltac1:(pose proof (partition_tl_means_true l tl fl f el H H0 H1)).
  ltac1:(pose proof (partition_fl_means_false l tl fl f el H H0 H2)).
  rewrite H3 in H4.
  discriminate.
}
apply Decidable.not_and in H1.
{
  apply H1.
}
{
  unfold Decidable.decidable.
  ltac1:(pose proof (elements_in_partition _ _ H el) as T1).
  do 3 (rewrite <- elem_of_list_In in T1).
  ltac1:(pose proof (H0) as H0').
  rewrite T1 in H0.
  clear T1.
  destruct H0.
  {
    left.
    apply H0.
  }
  {
    right.
    unfold not.
    intros.
    ltac1:(pose proof (partition_tl_means_true l tl fl f el H H0' H2)).
    ltac1:(pose proof (partition_fl_means_false l tl fl f el H H0' H0)).
    rewrite H3 in H4.
    discriminate.
  }
}
Qed.

Lemma partition_tl_true_equiv {A : Type} {_a_eqd : EqDecision A }:
  ∀ (l tl fl : list A) (f : A -> bool) (el : A),
  partition f l = (tl, fl) ->
  el ∈ l ->
  el ∈ tl <->
  f el = true
.
Proof.
intros.
split.
{
  intros.
  ltac1:(apply (partition_tl_means_true l tl fl f el H H0 H1)).
}
{
  intros.
  ltac1:(apply (partition_true_in_tl l tl fl f el H H0 H1)).
}
Qed.

Lemma partition_fl_false_equiv {A : Type} {_a_eqd : EqDecision A }:
  ∀ (l tl fl : list A) (f : A -> bool) (el : A),
  partition f l = (tl, fl) ->
  el ∈ l ->
  el ∈ fl <->
  f el = false
.
Proof.
intros.
ltac1:(pose proof (partition_tl_true_equiv l tl fl f el H H0)).
apply not_iff_compat in H1.
ltac1:(assert (el ∉ tl <-> el ∈ fl)).
{
  destruct H1.
  ltac1:(assert (el ∉ tl -> el ∈ fl)).
  {
    intros.
    ltac1:(pose proof (elements_in_partition _ _ H el) as T1).
    do 3 (rewrite <- elem_of_list_In in T1).
    rewrite T1 in H0.
    clear T1.
    destruct H0.
    {
      unfold not in H3.
      apply H3 in H0.
      destruct H0.
    }
    {
      apply H0.
    }
  }

  split.
  {
    apply H3.
  }
  {
    intros.
    ltac1:(pose proof (partition_tl_fl_disjunct l tl fl f el H H0)).
    destruct H5.
    {
      apply H5.
    }
    {
      unfold not in H5.
      apply H5 in H4.
      destruct H4.
    }
  }
}
rewrite H2 in H1.
rewrite not_true_iff_false in H1.
apply H1.
Qed.

Lemma u_extract_nonempty_m_meqn_is_nonempty_listset {Σ : StaticModel} :
      ∀ (u u' : listset Meqn) (meqn : Meqn),
        u_extract_nonempty_m_meqn_listset u = Some (meqn, u') -> ~~ meqn_m_empty meqn
.
Proof.
intros.
unfold u_extract_nonempty_m_meqn_listset in H.
ltac1:(resymde (partition meqn_m_empty (elements u)) P HeqP).
destruct l0.
{
  discriminate.
}
{
  inversion H.
  clear H.
  destruct (decide (meqn_m_empty meqn = true)) as [H3 | H3].
  {
    assert (m ∈ m :: l0) by (apply elem_of_list_here).
    ltac1:(pose proof (or_intror (m ∈ l) H)).
    do 2 (rewrite elem_of_list_In in H0).
    rewrite <- (elements_in_partition _ _ HeqP) in H0.
    rewrite <- elem_of_list_In in H0.
    ltac1:(pose proof (partition_fl_means_false _ _ _ _ _ HeqP H0 H)).
    rewrite H1 in H4.
    rewrite H4 in H3.
    discriminate.
  }
  {
    rewrite eq_true_not_negb_iff in H3.
    rewrite H3.
    reflexivity.
  }
}
Qed.

Lemma u_extract_overlapping_meqns_in_ls_meqn_listset {Σ : StaticModel} :
      ∀ (u u' : listset Meqn) (v : variable) (ls_meqn : listset Meqn) (meqn : Meqn),
        u_extract_overlapping_meqns_listset u v = (ls_meqn, u') ->
        meqn ∈ elements u ->
        (meqn ∈ ls_meqn <-> v ∈ get_var_part meqn)
.
Proof.
intros u u' v ls_meqn meqn H H'.
split.
{
  intros H1.
  unfold u_extract_overlapping_meqns_listset in H.
  ltac1:(repeat case_match; simplify_eq).
  rewrite elem_of_list_to_set in H1.
  ltac1:(pose proof(H1) as H2).
  remember (λ x : Meqn, bool_decide (v ∈ get_var_part x)) as f.
  ltac1:(pose proof (elements_in_partition f) (elements u) l l0 H0 meqn as T1).
  do 3 (rewrite <- elem_of_list_In in T1).
  destruct T1 as [_ T1].
  ltac1:(pose proof(or_introl) as T2).
  specialize (T2 (meqn ∈ l) (meqn ∈ l0)) as T2.
  apply T2 in H1.
  apply T1 in H1.
  clear T1.
  clear T2.
  ltac1:(pose proof (partition_tl_means_true (elements u) l l0 f meqn H0 H1 H2) as H3).
  rewrite Heqf in H3.
  apply bool_decide_eq_true_1 in H3.
  assumption.
}
{
  intros.
  unfold u_extract_overlapping_meqns_listset in H.
  ltac1:(repeat case_match; simplify_eq).
  rewrite elem_of_list_to_set.
  remember (λ x : Meqn, bool_decide (v ∈ get_var_part x)) as f.
  assert (f meqn = true).
  {
    rewrite Heqf.
    rewrite bool_decide_eq_true.
    assumption.
  }
  ltac1:(pose proof (partition_true_in_tl (elements u) l l0 f meqn H1 H' H) as H3).
  assumption.
}
Qed.

Lemma u_extract_overlapping_meqns_in_u'_listset {Σ : StaticModel} :
  ∀ (u u' : listset Meqn) (v : variable) (ls_meqn : listset Meqn) (meqn : Meqn),
    u_extract_overlapping_meqns_listset u v = (ls_meqn, u') ->
    meqn ∈ elements u ->
    (meqn ∈ elements u' <-> v ∉ get_var_part meqn)
.
Proof.
intros u u' v ls_meqn meqn H H'.
split.
{
  intros H1.
  unfold u_extract_overlapping_meqns_listset in H.
  ltac1:(repeat case_match; simplify_eq).
  rewrite elem_of_elements in H1.
  rewrite elem_of_list_to_set in H1.
  ltac1:(pose proof(H1) as H2).
  remember (λ x : Meqn, bool_decide (v ∈ get_var_part x)) as f.
  ltac1:(pose proof (elements_in_partition f) (elements u) l l0 H0 meqn as T1).
  do 3 (rewrite <- elem_of_list_In in T1).
  destruct T1 as [_ T1].
  ltac1:(pose proof(or_intror) as T2).
  specialize (T2 (meqn ∈ l) (meqn ∈ l0)) as T2.
  apply T2 in H1.
  apply T1 in H1.
  clear T1.
  clear T2.
  ltac1:(pose proof (partition_fl_means_false (elements u) l l0 f meqn H0 H1 H2) as H3).
  rewrite Heqf in H3.
  apply bool_decide_eq_false_1 in H3.
  assumption.
}
{
  intros.
  unfold u_extract_overlapping_meqns_listset in H.
  ltac1:(repeat case_match; simplify_eq).
  rewrite elem_of_elements.
  rewrite elem_of_list_to_set.
  remember (λ x : Meqn, bool_decide (v ∈ get_var_part x)) as f.
  assert (f meqn = false).
  {
    rewrite Heqf.
    rewrite bool_decide_eq_false.
    assumption.
  }
ltac1:(pose proof (partition_fl_false_equiv (elements u) l l0 f meqn H1 H') as H3).
rewrite <- H3 in H.
assumption.
}
Qed.

Lemma u_extract_overlapping_meqns_insert_equiv_listset {Σ : StaticModel} :
      ∀ (u u' : listset Meqn) (v : variable) (ls_meqn : listset Meqn),
        u_extract_overlapping_meqns_listset u v = (ls_meqn, u') ->
        elements u ≡ₚ elements ls_meqn ++ elements u'
.
Proof.
intros.

assert (u ≡ u' ∪ ls_meqn).
{
  unfold u_extract_overlapping_meqns_listset in H.
  remember (partition (λ x : Meqn, bool_decide (v ∈ get_var_part x)) (elements u)) as p.
  remember (λ x : Meqn, bool_decide (v ∈ get_var_part x)) as f.
  destruct p.
  symmetry in Heqp.
  remember (elements u) as elu.
  symmetry in Heqelu.

  ltac1:(pose proof (set_equiv u (u' ∪ ls_meqn))).
  apply H0.
  clear H0.
  intros.
  split.
  {
    intros.
    rewrite <- Heqelu in Heqp.
    rewrite <- elem_of_elements in H0.
    rewrite elem_of_list_In in H0.
    rewrite (elements_in_partition f (elements u) Heqp x) in H0.
    do 2 (rewrite <- elem_of_list_In in H0).
    rewrite Logic.or_comm in H0.
    do 2 (rewrite <- (@elem_of_list_to_set _ (listset Meqn) _ _ _ _ _) in H0).
    rewrite <- elem_of_union in H0.
    inversion H.
    subst.
    assumption.
  }
  {
    intros.
    rewrite <- Heqelu in Heqp.
    inversion H.
    rewrite <- H2 in H0.
    rewrite <- H3 in H0.
    rewrite elem_of_union in H0.
    do 2 (rewrite (@elem_of_list_to_set _ (listset Meqn) _ _ _ _ _) in H0).
    rewrite Logic.or_comm in H0.
    do 2 (rewrite elem_of_list_In in H0).
    rewrite <- (elements_in_partition f (elements u) Heqp x) in H0.
    rewrite <- elem_of_list_In in H0.
    rewrite elem_of_elements in H0.
    assumption.
  }
}
ltac1:(rewrite union_comm in H0).
rewrite H0.
assert (ls_meqn ## u').
{
  rewrite elem_of_disjoint.
  intros.
  rewrite set_equiv in H0.
  setoid_rewrite elem_of_union in H0.
  ltac1:(pose proof (or_introl (x ∈ u') H1)).
  specialize (H0 x).
  rewrite <- H0 in H3.
  rewrite <- elem_of_elements in H2, H3.
  rewrite (u_extract_overlapping_meqns_in_ls_meqn_listset _ _ _ _ _ H H3) in H1.
  rewrite (u_extract_overlapping_meqns_in_u'_listset _ _ _ _ _ H H3) in H2.
  apply H2 in H1.
  destruct H1.
}
apply elements_disj_union.
assumption.
Qed.

(* QQ TODO: fix this together *)

Program Definition U_listset_ops {Σ : StaticModel} : U_ops := {|
  U := listset Meqn;

  u_insert := (λ ls meqn, singleton meqn ∪ ls);
  u_map := (λ u f, f <$> u);

  u_extract_nonempty_m_meqn := u_extract_nonempty_m_meqn_listset;
  
  u_extract_overlapping_meqns := u_extract_overlapping_meqns_listset;
|}.
Next Obligation.
intros.
apply NoDup_elements.
Qed.
Next Obligation.
intros.
simpl.
rewrite elem_of_elements in H.
assert ({[meqn]} ∪ u ≡ u).
{
  rewrite set_equiv.
  split.
  {
  intros.
  rewrite elem_of_union in H0.
  destruct H0.
    {
      rewrite elem_of_singleton in H0.
      rewrite H0.
      assumption.
    }
    {
      assumption.
    }
  }
  {
    intros.
    rewrite elem_of_union.
    right.
    assumption.
  }
}
rewrite H0.
reflexivity.
Qed.
Next Obligation.
intros.
simpl.
apply elements_union_singleton.
rewrite <- elem_of_elements.
assumption.
Qed.
Next Obligation.
intros.
apply (u_extract_nonempty_m_removes_element_listset _ _ _ H).
Qed.
Next Obligation.
intros Σ.
exact u_extract_nonempty_m_insert_equiv_listset.
Qed.
Next Obligation.
intros.
apply (u_extract_nonempty_m_meqn_is_nonempty_listset _ _ _ H).
Qed.
Next Obligation.
intros Σ.
exact u_extract_overlapping_meqns_in_ls_meqn_listset.
Qed.
Next Obligation.
intros Σ.
exact u_extract_overlapping_meqns_in_u'_listset.
Qed.
Next Obligation.
intros Σ.
exact u_extract_overlapping_meqns_insert_equiv_listset.
Qed.

Definition is_compact_up_to_var {Σ : StaticModel} (u_ops : U_ops) (u : U) (v : variable) : Prop :=
  ∀ (meqn meqn' : Meqn),
    meqn ∈ elements u ->
    meqn' ∈ elements u ->
    meqn ≠ meqn' ->
    v ∉ get_var_part meqn \/ v ∉ get_var_part meqn'
.

(* That u is compact on vars that are not in gv *)
Definition is_compact_up_to_vars {Σ : StaticModel} (u_ops : U_ops) (u : U) (gv : gset variable) : Prop :=
  ∀ (v : variable),
    v ∈ (u_get_vars u ∖ gv) ->
    is_compact_up_to_var u_ops u v
.

Definition is_compact {Σ : StaticModel} {u_ops : U_ops} (u : U) : Prop :=
  ∀ (meqn meqn' : Meqn),
    meqn ∈ elements u ->
    meqn' ∈ elements u ->
    meqn ≠ meqn' ->
    get_var_part meqn ∩ get_var_part meqn' ≡ ∅ 
.

Definition compactify_by_var_extract_and_comp {Σ : StaticModel} (u_ops : U_ops) (u : U) (v : variable) : (Meqn * U)%type :=
  let '(to_compact, u_rest) := u_ops.(u_extract_overlapping_meqns) u v in
    (⋃ elements to_compact, u_rest)
.

Definition compactify_by_var {Σ : StaticModel} (u_ops : U_ops) (u : U) (v : variable) : U :=
  let '(to_compact, u_rest) := u_extract_overlapping_meqns u v in
    match elements to_compact with
      | [] => u
      | _ => u_insert u_rest (⋃ (elements to_compact))
    end
.

Fixpoint compactify_by_vars {Σ : StaticModel} (u_ops : U_ops) (u : U) (lv : list variable) : U :=
  match lv with
    | [] => u
    | x :: xs => compactify_by_vars u_ops (compactify_by_var u_ops u x) xs
  end
.

Definition compactify {Σ : StaticModel} {u_ops : U_ops} (u : U) : U :=
  compactify_by_vars u_ops u ((elements ∘ u_get_vars) u)
.

Lemma meqn_get_nonvar_part_mjoin_union_list {Σ : StaticModel} :
  ∀ (lm : list Meqn) (gv : gset variable) (lt : list (TermOver BuiltinOrVar)),
    ⋃ lm = (gv, lt) -> lt = mjoin (get_nonvar_part <$> lm)
.
Proof.
intros lm.
induction lm.
{
  intros.
  rewrite union_list_nil in H.
  unfold empty in H.
  unfold meqn_empty in H.
  inversion H.
  rewrite fmap_nil.
  simpl.
  reflexivity.
}
{
  intros.
  rewrite union_list_cons in H.
  inversion H.
  destruct (⋃ lm).
  destruct a.
  rewrite fmap_cons.
  simpl in *.
  rewrite app_inv_head_iff.
  assert ((g, l) = (g, l)) by reflexivity.
  specialize (IHlm g l H0).
  assumption.
}
Qed.

Lemma meqn_union_list_elem_of_get_nonvar_part {Σ : StaticModel} :
  ∀ (lm : list Meqn) (t : TermOver BuiltinOrVar), t ∈ get_nonvar_part (⋃ lm) -> Exists (fun meqn => t ∈ get_nonvar_part meqn) lm
.
Proof.
setoid_rewrite Exists_exists.
intros.
remember (⋃ lm) as LM.
symmetry in HeqLM.
destruct LM.
apply meqn_get_nonvar_part_mjoin_union_list in HeqLM.
unfold get_nonvar_part in H.
simpl in H.
rewrite HeqLM in H.
rewrite elem_of_list_join in H.
destruct H as [l' [H H']].
rewrite elem_of_list_fmap in H'.
destruct H' as [meqn' [H' H'']].
exists meqn'.
split.
{
  assumption.
}
{
  rewrite H' in H.
  assumption.
}
Qed.

Lemma union_list_valid_meqn_keeps_valid {Σ : StaticModel} :
  ∀ (lm : list Meqn), Forall (fun meqn => meqn_valid meqn) lm -> lm ≠ [] -> meqn_valid (⋃ lm)
.
Proof.
intros lm.
rewrite Forall_forall.
induction lm.
{
  intros.
  unfold not in H0.
  assert (@nil Meqn = []) by reflexivity.
  specialize (H0 H1).
  destruct H0.
}
{
  intros.
  unfold meqn_valid.
  split.
  {
    unfold meqn_left_valid.
    setoid_rewrite var_elem_of_meqn.
    setoid_rewrite elem_of_union_list.
    assert (a ∈ a :: lm) by (apply elem_of_list_here).
    specialize (H _ H1).
    unfold meqn_valid in H.
    destruct H as [H _].
    unfold meqn_left_valid in H.
    destruct H as [v' H].
    exists v'.
    exists a.
    split.
    {
      assumption.
    }
    {
      rewrite <- var_elem_of_meqn.
      assumption.
    }
  }
  {
    unfold meqn_right_valid.
    intros.
    destruct (term_is_nonvar t) eqn:H2.
    {
      reflexivity.
    }
    {
      apply meqn_union_list_elem_of_get_nonvar_part in H1.
      rewrite Exists_exists in H1.
      destruct H1 as [meqn' [H1 H1']].
      specialize (H meqn' H1).
      unfold meqn_valid in H.
      destruct H as [_ H].
      unfold meqn_right_valid in H.
      specialize (H t H1').
      destruct (term_is_nonvar t) eqn:H3.
        {
          discriminate H2.
        }
      {
        inversion H.
      }
    }
  }
}
Qed.

Lemma compactify_by_var_meqn_inv_rg {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v : variable),
      compactify_by_var u_ops u v = u' ->
      ∀ (meqn : Meqn), (meqn ∈ elements u ∧ v ∉ get_var_part meqn) ∨
      (∃ (lm : list Meqn), meqn = (⋃ lm) ∧ v ∈ get_var_part meqn ∧ ∀ (meqn' : Meqn), meqn' ∈ lm <-> meqn' ∈ elements u ∧ v ∈ get_var_part meqn') ->
      ∃ (meqn'' : Meqn), meqn ≡ meqn'' ∧  meqn'' ∈ elements u'
.
Proof.
intros.
destruct H0 as [[H0 H1] | [lm [H0 [H1 H2]]]].
{
  exists meqn.
  split.
  {
    reflexivity.
  }
  {
    unfold compactify_by_var in H.
    ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
    ltac1:(resymde (elements l) EL HeqEL).
    {
      rewrite H in H0.
      assumption.
    }
    {
      ltac1:(pose proof H0).
      rewrite (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H2.
      destruct H2.
      {
        rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H0) in H2.
        apply H1 in H2.
        destruct H2.
      }
      {
        rewrite (u_insert_elem_of _ _ _ H).
        left.
        assumption.
      }
    }
  }
}
{
  unfold compactify_by_var in H.
  ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
  assert (∀ meqn', meqn' ∈ l <-> meqn' ∈ elements u ∧ v ∈ get_var_part meqn').
  {
    split.
    {
      intros.
      ltac1:(pose proof H3).
      ltac1:(apply (@or_introl _ (meqn' ∈ elements u0)) in H3).
      rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H3.
      rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H3) in H4.
      apply (conj H3 H4).
    }
    {
      intros.
      destruct H3 as [H3 H4].
      rewrite <- (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H3) in H4.
      assumption.
    }
  }
  ltac1:(resymde (elements l) EL HeqEL).
  {
    setoid_rewrite <- H3 in H2.
    setoid_rewrite <- elem_of_elements in H2.
    assert (lm = []).
    {
      apply elem_of_nil_inv.
      intros.
      intros Hcontra.
      specialize (H2 x).
      rewrite HeqEL in H2.
      rewrite H2 in Hcontra.
      apply not_elem_of_nil in Hcontra.
      destruct Hcontra.
    }
    rewrite H4 in H0.
    rewrite union_list_nil in H0.
    rewrite H0 in H1.
    unfold get_var_part in H1.
    simpl in H1.
    apply not_elem_of_empty in H1.
    destruct H1.
  }
  setoid_rewrite <- H3 in H2.
  clear H3.
  {
    remember (⋃ (m :: EL)) as meqnc.
    exists meqnc.
    split.
    {
      ltac1:(pose proof (set_equiv meqn meqnc)).
      rewrite H3.
      clear H3.
      intros.
      split.
      {
        intros.
        ltac1:(pose proof (elem_of_union_list lm)).
        setoid_rewrite <- H0 in H4.
        specialize (H4 x).
        rewrite H4 in H3.
        clear H4.
        destruct H3 as [meqn' [H3 H4]].
        rewrite H2 in H3.
        ltac1:(pose proof (elem_of_union_list (elements l) x)).
        destruct H5 as [_ H5].
        ltac1:(ospecialize (H5 _)).
        {
          rewrite <- elem_of_elements in H3.
          exists meqn'.
          apply (conj H3 H4).
        }
        rewrite Heqmeqnc.
        rewrite <- HeqEL.
        assumption.
      }
      {
        intros.
        ltac1:(pose proof (elem_of_union_list (elements l))).
        setoid_rewrite HeqEL in H4.
        setoid_rewrite <- Heqmeqnc in H4.
        specialize (H4 x).
        rewrite H4 in H3.
        clear H4.
        destruct H3 as [meqn' [H3 H4]].
        rewrite <- HeqEL in H3.
        rewrite elem_of_elements in H3.
        rewrite <- H2 in H3.
        ltac1:(pose proof (elem_of_union_list lm x)).
        destruct H5 as [_ H5].
        ltac1:(ospecialize (H5 _)).
        {
          exists meqn'.
          apply (conj H3 H4).
        }
        rewrite H0.
        assumption.
      }
    }
    {
      rewrite (u_insert_elem_of _ _ _ H).
      destruct(decide (meqnc ∈ elements u0)) as [H3 | H3].
      {
        left.
        assumption.
      }
      {
        right.
        split.
        {
          reflexivity.
        }
        {
          assumption.
        }
      }
    }
  }
}
Qed.

Lemma compactify_by_var_v_not_in_meqn {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v : variable),
      compactify_by_var u_ops u v = u' ->
      ∀ (meqn : Meqn), v ∉ get_var_part meqn ->
      meqn ∈ elements u <-> meqn ∈ elements u'
.
Proof.
split.
{
  intros.
  unfold compactify_by_var in H.
  ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
  ltac1:(resymde (elements l) EL HeqEL).
  {
    rewrite H in H1.
    assumption.
  }
  {
    rewrite (u_insert_elem_of _ _ _ H).
    left.
    rewrite <- (u_extract_overlapping_meqns_in_u' _ _ _ _ _ HeqUEO H1) in H0.
    assumption.
  }
}
{
  intros.
  unfold compactify_by_var in H.
  ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
  ltac1:(resymde (elements l) EL HeqEL).
  {
    rewrite H.
    assumption.
  }
  {
    rewrite (u_insert_elem_of _ _ _ H) in H1.
    destruct H1 as [H1 | [H1 H2]].
    {
      ltac1:(pose proof (or_intror (meqn ∈ l) H1)).
      rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H2.
      assumption.
    }
    {
      assert (m ∈ elements l) by (rewrite HeqEL; apply elem_of_list_here).
      ltac1:(pose proof H3 as H3').
      rewrite elem_of_elements in H3.
      ltac1:(pose proof (or_introl (m ∈ elements u0) H3)).
      rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H4.
      rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H4) in H3.
      ltac1:(pose proof (elem_of_union_list (elements l) (var_to_term v))).
      setoid_rewrite <- var_elem_of_meqn in H5.
      destruct H5 as [_ H5].
      ltac1:(ospecialize (H5 _)).
      {
        exists m.
        apply (conj H3' H3).
      }
      rewrite <- HeqEL in H1.
      rewrite <- H1 in H5.
      apply H0 in H5.
      destruct H5.
    }
  }
}
Qed.

Lemma compactify_by_var_v_in_meqn {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v : variable),
      compactify_by_var u_ops u v = u' ->
      ∀ (meqn : Meqn), v ∈ get_var_part meqn ->
      meqn ∈ elements u -> Exists (fun meqn' => ∀ t : TermOver BuiltinOrVar, t ∈ meqn -> t ∈ meqn') (elements u')
.
Proof.
intros.
rewrite Exists_exists.
unfold compactify_by_var in H.
ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
ltac1:(resymde (elements l) EL HeqEL).
{
  exists meqn.
  split.
  {
    rewrite <- H.
    assumption.
  }
  {
    intros.
    assumption.
  }
}
{
  remember (⋃ (m :: EL)) as meqnc.
  exists meqnc.
  split.
  {
    destruct (decide (meqnc ∈ elements u0)) as [H2 | H2].
    {
      ltac1:(pose proof H2 as H2').
      apply u_insert_id in H2.
      rewrite H in H2.
      rewrite <- H2 in H2'.
      assumption.
    }
    {
      apply u_insert_add in H2.
      rewrite H in H2.
      rewrite H2.
      apply elem_of_list_here.
    }
  }
  {
    intros.
    ltac1:(pose proof (elem_of_union_list (elements l))).
    specialize (H3 t).
    rewrite <- HeqEL in Heqmeqnc.
    rewrite <- Heqmeqnc in H3.
    rewrite H3.
    clear H3.
    exists meqn.
    rewrite <- (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H1) in H0.
    rewrite <- elem_of_elements in H0.
    apply (conj H0 H2).
  }
}
Qed.


Lemma compactify_by_var_is_compact_up_to_var {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v : variable),
      compactify_by_var u_ops u v = u' ->
      is_compact_up_to_var u_ops u' v
.
Proof.
unfold is_compact_up_to_var.
intros.
unfold compactify_by_var in H.
ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
ltac1:(resymde (elements l) EL HeqEL).
{
  left.
  rewrite <- H in H0.
  destruct (decide (v ∈ get_var_part meqn)) as [H3 | H3].
  {
    rewrite <- (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H0) in H3.
    rewrite <- elem_of_elements in H3.
    rewrite HeqEL in H3.
    apply not_elem_of_nil in H3.
    destruct H3.
  }
  {
    assumption.
  }
}
{
  remember (⋃ elements l) as meqnv.
  assert (∀ (meqn'' : Meqn), meqn'' ∈ elements u0 -> v ∉ get_var_part meqn'').
  {
    intros.

    assert (meqn'' ∈ elements u).
    {
      ltac1:(pose proof(u_extract_overlapping_meqns_disjunct u u0 v l meqn'' HeqUEO)).
      ltac1:(pose proof (or_intror)).
      specialize (H5 (meqn'' ∈ l) (meqn'' ∈ elements u0)).
      apply H5 in H3.
      rewrite <- H4 in H3.
      assumption.
    }

    ltac1:(pose proof(u_extract_overlapping_meqns_in_u' u u0 v l meqn'' HeqUEO H4)).
    rewrite H5 in H3.
    assumption.
  }
  ltac1:(pose proof (u_insert_elem_of u0 u' (⋃ (m :: EL)) H)).
  rewrite (H4 meqn) in H0.
  destruct H0.
  {
    specialize (H3 meqn).
    apply H3 in H0.
    left.
    assumption.
  }
  {
    rewrite (H4 meqn') in H1.
    destruct H1.
    {
      specialize (H3 meqn').
      apply H3 in H1.
      right.
      assumption.
    }
    {
      destruct H0 as [H0 _].
      destruct H1 as [H1 _].
      rewrite <- H1 in H0.
      apply H2 in H0.
      destruct H0.
    }
  }
}
Qed.

Lemma compactify_by_var_keeps_get_vars {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v : variable),
      compactify_by_var u_ops u v = u' ->
      ∀ (v' : variable), v' ∈ u_get_vars u <-> v' ∈ u_get_vars u'
.
Proof.
intros u_ops u u' v H.
unfold compactify_by_var in H.
remember (u_extract_overlapping_meqns u v) as UEO.
destruct UEO.
symmetry in HeqUEO.
remember (⋃ elements l) as c_meqn.
assert (∀ (v'' : variable), v'' ∈ u_get_vars u <-> v'' ∈ u_get_vars u0 ∨ v'' ∈ get_var_part c_meqn).
{
  split.
  {
    intros.
    rewrite (u_extract_overlapping_meqns_keeps_get_vars u u0 v v'' l HeqUEO) in H0.
    destruct H0.
    {
      left.
      assumption.
    }
    {
      right.
      rewrite get_vars_of_var_part_listset_meqns_equiv in H0.
      destruct H0 as [meqn [H0 H1]].
      rewrite var_elem_of_meqn in H1.
      rewrite var_elem_of_meqn.
      unfold var_to_term.
      rewrite Heqc_meqn.
      ltac1:(pose proof(elem_of_union_list (elements l) (t_over (bov_variable v'')))).
      rewrite H2.
      exists meqn.
      rewrite <- elem_of_elements in H0.
      apply (conj H0 H1).
    }
  }
  {
    intros.
    destruct H0.
    {
      ltac1:(pose proof (or_introl (v'' ∈ get_vars_of_var_part_listset_meqns l) H0)).
      rewrite (u_extract_overlapping_meqns_keeps_get_vars u u0 v v'' l HeqUEO).
      assumption.
    }
    {
      rewrite var_elem_of_meqn in H0.
      rewrite Heqc_meqn in H0.
      rewrite (elem_of_union_list (elements l) (var_to_term v'')) in H0.
      destruct H0 as [meqn [H0 H1]].
      rewrite elem_of_elements in H0.
      ltac1:(pose proof (or_introl (meqn ∈ elements u0) H0)).
      rewrite <- (u_extract_overlapping_meqns_disjunct u u0 v l meqn HeqUEO) in H2.
      rewrite <- var_elem_of_meqn in H1.
      ltac1:(pose proof (conj H2 H1)).
      rewrite u_get_vars_exists_meqn.
      rewrite Exists_exists.
      exists meqn.
      assumption.
    }
  }
}
assert (∀ (v'' : variable), v'' ∈ get_var_part c_meqn <-> v'' ∈ get_vars_of_var_part_listset_meqns {[c_meqn]}).
{
  setoid_rewrite get_vars_of_var_part_listset_meqns_equiv.
  split.
  {
    intros.
    exists c_meqn.
    rewrite elem_of_singleton.
    assert (c_meqn = c_meqn) by reflexivity.
    apply (conj H2 H1).
  }
  {
    intros.
    destruct H1 as [meqn [H1 H2]].
    rewrite elem_of_singleton in H1.
    rewrite H1 in H2.
    assumption.
  }
}
remember (elements l) as EL.
destruct EL.
{
  rewrite H.
  reflexivity.
}
{
  assert (H2': elements (u_insert u0 c_meqn) ≡ₚ elements u') by (rewrite H; reflexivity).
  ltac1:(pose proof (u_insert_keeps_u_get_vars u0 u' c_meqn H2')).
  setoid_rewrite H0.
  setoid_rewrite H2.
  reflexivity.
}
Qed.

Lemma is_compact_up_to_var_at_most_one_meqn_with_var {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u : U) (v : variable) (meqn : Meqn),
      is_compact_up_to_var u_ops u v ->
      meqn ∈ elements u ->
      v ∈ get_var_part meqn ->
      ∀ (meqn' : Meqn), meqn' ∈ elements u ->
      meqn ≠ meqn' ->
      v ∉ get_var_part meqn'
.
Proof.
intros.
unfold is_compact_up_to_var in H.
specialize (H meqn meqn' H0 H2 H3).
destruct H.
{
  unfold not in H.
  apply H in H1.
  destruct H1.
}
{
  assumption.
}
Qed.

Lemma compactify_by_var_meqn_in_v_in {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v : variable),
    compactify_by_var u_ops u v = u' ->
    ∀ (meqn : Meqn), meqn ∈ elements u ->
    v ∈ get_var_part meqn ->
    ∃ (lm : list Meqn), (⋃ lm) ∈ elements u' ∧ ∀ (meqn' : Meqn), meqn' ∈ lm <-> meqn' ∈ elements u ∧ v ∈ get_var_part meqn'
.
Proof.
intros.
unfold compactify_by_var in H.
ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
ltac1:(resymde (elements l) EL HeqEL).
{
  rewrite <- (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H0) in H1.
  rewrite <- elem_of_elements in H1.
  rewrite HeqEL in H1.
  apply not_elem_of_nil in H1.
  destruct H1.
}
{
  exists (elements l).
  split.
  {
    rewrite (u_insert_elem_of _ _ _ H).
    right.
    split.
    {
      rewrite HeqEL.
      reflexivity.
    }
    {
      intros Hcontra.
      ltac1:(pose proof (or_intror (⋃ (m :: EL) ∈ l) Hcontra)).
      rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H2.
      rewrite (u_extract_overlapping_meqns_in_u' _ _ _ _ _ HeqUEO H2) in Hcontra.
      assert (v ∈ get_var_part (⋃ (m :: EL))).
      {
        ltac1:(pose proof (elem_of_union_list (elements l) (var_to_term v))).
        setoid_rewrite <- var_elem_of_meqn in H3.
        rewrite <- HeqEL.
        rewrite H3.
        clear H3.
        exists m.
        assert (m ∈ elements l) by (rewrite HeqEL; apply elem_of_list_here).
        ltac1:(pose proof (or_introl (m ∈ elements u0) H3)).
        ltac1:(pose proof H3).
        rewrite elem_of_elements in H3, H4.
        rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H4.
        rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H4) in H3.
        apply (conj H5 H3).
      }
      apply Hcontra in H3.
      destruct H3.
    }
  }
  {
    split.
    {
      intros.
      rewrite elem_of_elements in H2.
      ltac1:(pose proof (or_introl (meqn' ∈ elements u0) H2)).
      rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ meqn' HeqUEO) in H3.
      rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H3) in H2.
      apply (conj H3 H2).
    }
    {
      intros.
      destruct H2 as [H3 H4].
      rewrite <- (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H3) in H4.
      rewrite elem_of_elements.
      assumption.
    }
  }
}
Qed.

Lemma compactify_by_var_meqn_only_in_u' {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (v : variable), compactify_by_var u_ops u v = u' ->
    ∀ (meqn : Meqn), meqn ∉ elements u ->
    meqn ∈ elements u' ->
    ∃ (lm : list Meqn), lm ≠ [] ∧ ⋃ lm = meqn ∧ ∀ meqn' : Meqn, meqn' ∈ lm ↔ meqn' ∈ elements u ∧ v ∈ get_var_part meqn'
.
Proof.
intros.
unfold compactify_by_var in H.
ltac1:(resymde (u_extract_overlapping_meqns u v) UEO HeqUEO).
ltac1:(resymde (elements l) EL HeqEL).
{
  rewrite H in H0.
  apply H0 in H1.
  destruct H1.
}
{
  exists (elements l).
  split.
  {
    apply (elem_of_not_nil m).
    rewrite HeqEL.
    apply elem_of_list_here.
  }
  {
    split.
    {
      {
        destruct (decide (v ∈ get_var_part meqn)) as [H2 | H2].
        {
          rewrite (u_insert_elem_of _ _ _ H) in H1.
          destruct H1.
          {
            ltac1:(pose proof (or_intror (meqn ∈ l) H1)).
            rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H3.
            rewrite (u_extract_overlapping_meqns_in_u' _ _ _ _ _ HeqUEO H3) in H1.
            apply H1 in H2.
            destruct H2.
          }
          {
            destruct H1 as [H1 H1'].
            rewrite H1.
            rewrite <- HeqEL.
            reflexivity.
          }
        }
        {
          rewrite (u_insert_elem_of _ _ _ H) in H1.
          destruct H1.
          {
            assert (v ∈ get_var_part meqn).
            {
              ltac1:(pose proof (or_intror (meqn ∈ l) H1)).
              rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H3.
              apply H0 in H3.
              destruct H3.
            }
            apply H2 in H3.
            destruct H3.
          }
          {
            destruct H1 as [H1 H1'].
            rewrite H1.
            rewrite HeqEL.
            reflexivity.
          }
        }
      }
    }
    {
      split.
      {
        intros.
        rewrite elem_of_elements in H2.
        ltac1:(pose proof (or_introl (meqn' ∈ elements u0) H2)).
        rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ meqn' HeqUEO) in H3.
        rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H3) in H2.
        apply (conj H3 H2).
      }
      {
        intros.
        destruct H2 as [H3 H4].
        rewrite <- (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H3) in H4.
        rewrite elem_of_elements.
        assumption.
      }
    }
  }
}
Qed.

Lemma compactify_by_var_keeps_previous_compactness {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (v v' : variable),
      compactify_by_var u_ops u v' = u' ->
      is_compact_up_to_var u_ops u v ->
      is_compact_up_to_var u_ops u' v
.
Proof.
intros.
unfold is_compact_up_to_var.
intros.
destruct (decide (v ∈ get_var_part meqn)) as [H4 | H4].
{
  destruct (decide (v ∈ get_var_part meqn')) as [H5 | H5].
  {
    unfold compactify_by_var in H.
    ltac1:(resymde (u_extract_overlapping_meqns u v') UEO HeqUEO).
    ltac1:(resymde (elements l) EL HeqEL).
    {
      rewrite <- H in H1, H2.
      unfold is_compact_up_to_var in H0.
      apply (H0 meqn meqn' H1 H2 H3).
    }
    {
      rewrite (u_insert_elem_of _ _ _ H) in H1.
      destruct H1 as [H1 | [H1 H1']].
      {
        ltac1:(pose proof (or_intror (meqn ∈ l) H1)).
        rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H6.
        rewrite (u_insert_elem_of _ _ _ H) in H2.
        destruct H2 as [H2 | [H2 H2']].
        {
          ltac1:(pose proof (or_intror (meqn' ∈ l) H2)).
          rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H7.
          unfold is_compact_up_to_var in H0.
          apply (H0 meqn meqn' H6 H7 H3).
        }
        {
          ltac1:(pose proof (elem_of_union_list (elements l) (var_to_term v))).
          setoid_rewrite <- var_elem_of_meqn in H7.
          rewrite <- HeqEL in H2.
          rewrite <- H2 in H7.
          rewrite H7 in H5.
          clear H7.
          destruct H5 as [meqn'' [H5 H5']].
          rewrite elem_of_elements in H5.
          ltac1:(pose proof (or_introl (meqn'' ∈ elements u0) H5)).
          rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H7.
          destruct (decide (meqn = meqn'')) as [H8 | H8].
          {
            rewrite (u_extract_overlapping_meqns_in_u' _ _ _ _ _ HeqUEO H6) in H1.
            rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H7) in H5.
            rewrite H8 in H1.
            apply H1 in H5.
            destruct H5.
          }
          {
            unfold is_compact_up_to_var in H0.
            specialize (H0 meqn meqn'' H6 H7 H8).
            destruct H0.
            {
              left.
              assumption.
            }
            {
              apply H0 in H5'.
              destruct H5'.
            }
          }
        }
      }
      {
        rewrite (u_insert_elem_of _ _ _ H) in H2.
        destruct H2 as [H2 | [H2 H2']].
        {
          ltac1:(pose proof (elem_of_union_list (elements l) (var_to_term v))).
          setoid_rewrite <- var_elem_of_meqn in H6.
          rewrite <- HeqEL in H1.
          rewrite <- H1 in H6.
          rewrite H6 in H4.
          clear H6.
          destruct H4 as [meqn'' [H4 H4']].
          rewrite elem_of_elements in H4.
          ltac1:(pose proof (or_introl (meqn'' ∈ elements u0) H4)).
          rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H6.
          ltac1:(pose proof (or_intror (meqn' ∈ l) H2)).
          rewrite <- (u_extract_overlapping_meqns_disjunct _ _ _ _ _ HeqUEO) in H7.
          destruct (decide (meqn' = meqn'')) as [H8 | H8].
          {
            rewrite (u_extract_overlapping_meqns_in_u' _ _ _ _ _ HeqUEO H7) in H2.
            rewrite (u_extract_overlapping_meqns_in_ls_meqn _ _ _ _ _ HeqUEO H6) in H4.
            rewrite H8 in H2.
            apply H2 in H4.
            destruct H4.
          }
          {
            unfold is_compact_up_to_var in H0.
            specialize (H0 meqn' meqn'' H7 H6 H8).
            destruct H0.
            {
              right.
              assumption.
            }
            {
              apply H0 in H4'.
              destruct H4'.
            }
          }
        }
        {
          rewrite H1 in H3.
          rewrite H2 in H3.
          assert (⋃ (m :: EL) = ⋃ (m :: EL)) by reflexivity.
          apply H3 in H6.
          destruct H6.
        }
      }
    }
  }
  {
    right.
    assumption.
  }
}
{
  left.
  assumption.
}
Qed.

Lemma compactify_by_var_keeps_u_valid {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (v : variable), compactify_by_var u_ops u v = u' ->
    u_valid u ->
    u_valid u'
.
Proof.
unfold u_valid.
setoid_rewrite Forall_forall.
intros.
destruct (decide (x ∈ elements u)) as [H2 | H2].
{
  specialize (H0 x H2).
  assumption.
}
{
  ltac1:(pose proof (compactify_by_var_meqn_only_in_u' _ _ _ H _ H2 H1)).
  destruct H3 as [lm [H3 [H3' H3'']]].
  assert (∀ (meqn'' : Meqn), meqn'' ∈ lm -> meqn_valid meqn'').
  {
    intros.
    specialize (H3'' meqn'').
    rewrite H3'' in H4.
    destruct H4 as [H4 _].
    specialize (H0 _ H4).
    assumption.
  }
  destruct lm.
  {
    ltac1:(set_solver).
  }
  {
    unfold meqn_valid.
    rewrite <- H3'.
    split.
    {
      unfold meqn_left_valid.
      setoid_rewrite var_elem_of_meqn.
      setoid_rewrite elem_of_union_list.
      assert (m ∈ m :: lm) by (apply elem_of_list_here).
      specialize (H4 m H5).
      unfold meqn_valid in H4.
      destruct H4 as [H4 _].
      unfold meqn_left_valid in H4.
      destruct H4 as [v' H4].
      exists v'.
      exists m.
      split.
      {
        assumption.
      }
      {
        rewrite <- var_elem_of_meqn.
        assumption.
      }
    }
    {
      assert (∀ (t' : TermOver BuiltinOrVar), t' ∈ x <-> Exists (fun meqn => t' ∈ meqn) (m::lm)).
      {
        split.
        {
          intros.
          rewrite Exists_exists.
          rewrite <- H3' in H5.
          rewrite elem_of_union_list in H5.
          assumption.
        }
        {
          intros.
          rewrite Exists_exists in H5.
          rewrite <- H3'.
          rewrite elem_of_union_list.
          assumption.
        }
      }
      unfold meqn_right_valid.
      intros.
      apply meqn_union_list_elem_of_get_nonvar_part in H6.
      rewrite Exists_exists in H6.
      destruct H6 as [meqn' [H6 H6']].
      specialize (H4 meqn' H6).
      unfold meqn_valid in H4.
      destruct H4 as [_ H4].
      unfold meqn_right_valid in H4.
      specialize (H4 t H6').
      assumption.
    }
  }
}
Qed.

Lemma compcatify_by_var_keeps_up_of_u {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (v : variable), compactify_by_var u_ops u v = u' ->
  u_valid u ->
  up_of_u u ⊆ up_of_u u'
.
Proof.
intros.
rewrite elem_of_subseteq.
intros.
destruct x.
rewrite (up_of_valid_u_elem_of _ t t0 H0) in H1.
rewrite Exists_exists in H1.
destruct H1 as [meqn [H1 [H2 H3]]].
ltac1:(pose proof (compactify_by_var_keeps_u_valid _ _ _ H H0)).
rewrite (up_of_valid_u_elem_of _ t t0 H4).
rewrite Exists_exists.
destruct (decide (meqn ∈ elements u')) as [H5 | H5].
{
  exists meqn.
  apply (conj H5 (conj H2 H3)).
}
{
  destruct (decide (v ∈ get_var_part meqn)) as [H6 | H6].
  {
    ltac1:(pose proof (compactify_by_var_v_in_meqn _ _ _ _ H _ H6 H1)).
    rewrite Exists_exists in H7.
    destruct H7 as [meqn' [H7 H8]].
    exists meqn'.
    apply (conj H7 (conj (H8 _ H2) (H8 _ H3))).
  }
  {
    rewrite (compactify_by_var_v_not_in_meqn _ _ _ _ H _ H6) in H1.
    apply H5 in H1.
    destruct H1.
  }
}
Qed.

Lemma compcatify_by_var_keeps_unifier_of {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (v : variable), compactify_by_var u_ops u v = u' ->
  u_valid u ->
  ∀ (s : SubTMM), is_unifier_of s (elements (up_of_u u)) <-> is_unifier_of s (elements (up_of_u u'))
.
Proof.
unfold is_unifier_of.
split.
{
  setoid_rewrite Forall_forall.
  intros.
  destruct (decide (x ∈ elements (up_of_u u))) as [H3 | H3].
  {
    apply (H1 _ H3).
  }
  {
      rewrite elem_of_elements in H2, H3.
      ltac1:(pose proof (compactify_by_var_keeps_u_valid _ _ _ H H0)).
      destruct x.
      rewrite (up_of_valid_u_elem_of _ _ _ H0) in H3.
      rewrite (up_of_valid_u_elem_of _ _ _ H4) in H2.
      rewrite Exists_exists in H2.
      destruct H2 as [meqn [H2 H2']].
      rewrite <- Forall_Exists_neg in H3.
      rewrite Forall_forall in H3.
      specialize (H3 meqn).
      destruct (decide (meqn ∈ elements u)) as [H5 | H5].
    {
      specialize (H3 H5).
      apply H3 in H2'.
      destruct H2'.
    }
    {
      clear H3.
      ltac1:(pose proof (compactify_by_var_meqn_only_in_u' _ _ _ H _ H5 H2)).
      destruct H3 as [lm [H3 [H3' H3'']]].
      assert (∀ (meqn' : Meqn) (t : TermOver BuiltinOrVar), meqn' ∈ lm -> t ∈ meqn' -> sub_app_mm s t = sub_app_mm s (var_to_term v)).
      {
        intros.
        rewrite H3'' in H6.
        destruct H6 as [H6 H6'].
        ltac1:(pose proof H0 as H0').
        unfold u_valid in H0.
        rewrite Forall_forall in H0.
        specialize (H0 _ H6).
        rewrite var_elem_of_meqn in H6'.
        specialize (H1 (t1, var_to_term v)).
        ltac1:(pose proof (up_of_valid_u_elem_of _ t1 (var_to_term v) H0')).
        destruct H8 as [_ H8].
        rewrite Exists_exists in H8.
        ltac1:(ospecialize (H8 _)).
        {
          exists meqn'.
          apply (conj H6 (conj H7 H6')).
        }
      rewrite elem_of_elements in H1.
      apply (H1 H8).
      }
    rewrite <- H3' in H2'.
    setoid_rewrite elem_of_union_list in H2'.
    destruct H2' as [[meqn' [H7 H7']] [meqn'' [H8 H8']]].
    ltac1:(pose proof H6 as H6').
    specialize (H6 _ _ H7 H7').
    specialize (H6' _ _ H8 H8').
    rewrite H6.
    rewrite H6'.
    reflexivity.
    }
  }
}
{
  setoid_rewrite Forall_forall.
  intros.
  destruct (decide (x ∈ elements (up_of_u u'))) as [H3 | H3].
  {
    apply (H1 _ H3).
  }
  {
    ltac1:(pose proof (compcatify_by_var_keeps_up_of_u _ _ _ H H0)).
    rewrite elem_of_subseteq in H4.
    rewrite elem_of_elements in H2, H3.
    specialize (H4 x H2).
    apply H3 in H4.
    destruct H4.
  }
}
Qed.

Lemma compactify_by_vars_inv_fold {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (lv : list variable) (v : variable),
    compactify_by_vars u_ops u (v :: lv) = u' <-> compactify_by_vars u_ops (compactify_by_var u_ops u v) lv = u'
.
Proof.
split.
{
  intros.
  simpl in H.
  assumption.
}
{
  intros.
  simpl.
  assumption.
}
Qed.

Lemma compactify_by_vars_keeps_compactness {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (lv : list variable) (v : variable),
    compactify_by_vars u_ops u lv = u' ->
    is_compact_up_to_var u_ops u v ->
    is_compact_up_to_var u_ops u' v
.
Proof.
intros u_ops u u' lv.
revert u_ops u u'.
induction lv.
{
  intros.
  unfold compactify_by_vars in H.
  rewrite H in H0.
  assumption.
}
{
  intros.
  rewrite compactify_by_vars_inv_fold in H.
  remember (compactify_by_var u_ops u a) as CBVA.
  symmetry in HeqCBVA.
  ltac1:(pose proof (compactify_by_var_keeps_previous_compactness _ _ _ _ _ HeqCBVA H0)).
  apply (IHlv u_ops CBVA u' v H H1).
}
Qed.

Lemma compactify_by_vars_is_compact_up_to_vars {Σ : StaticModel} :
  ∀ (u_ops : U_ops) (u u' : U) (lv : list variable),
    compactify_by_vars u_ops u lv = u' ->
    is_compact_up_to_vars u_ops u' (u_get_vars u' ∖ list_to_set lv)
.
Proof.
intros u_ops u u' lv.
revert u_ops u u'.
induction lv.
{
  intros.
  unfold compactify_by_vars in H.
  unfold is_compact_up_to_vars.
  intros.
  simpl in H0.
  rewrite difference_empty in H0.
  rewrite difference_diag in H0.
  apply not_elem_of_empty in H0.
  destruct H0.
}
{
  intros.
  rewrite compactify_by_vars_inv_fold in H.
  remember (compactify_by_var u_ops u a) as CBVA.
  symmetry in HeqCBVA.
  specialize (IHlv u_ops CBVA u' H).
  apply compactify_by_var_is_compact_up_to_var in HeqCBVA as CompCBVA.
  unfold is_compact_up_to_vars.
  intros.
  unfold is_compact_up_to_var.
  intros.
  unfold is_compact_up_to_vars in IHlv.
  destruct (decide (v ∈ u_get_vars u' ∖ (u_get_vars u' ∖ list_to_set lv))) as [H4 | H4].
  {
    specialize (IHlv v H4).
    unfold is_compact_up_to_var in IHlv.
    apply (IHlv meqn meqn' H1 H2 H3).
  }
  {
    clear IHlv.
    rewrite elem_of_difference in H0.
    destruct H0 as [H0 H0'].
    rewrite elem_of_difference in H0'.
    rewrite not_and_r in H0'.
    destruct H0'.
    {
      apply H5 in H0.
      destruct H0.
    }
    {
      apply dec_stable in H5.
      rewrite elem_of_difference in H4.
      rewrite not_and_r in H4.
      destruct H4.
      {
        apply H4 in H0.
        destruct H0.
      }
      {
        apply dec_stable in H4.
        rewrite elem_of_difference in H4.
        destruct H4 as [H4 H4'].
        rewrite elem_of_list_to_set in H5, H4'.
        rewrite elem_of_cons in H5.
        destruct H5.
        {
          clear H4.
          ltac1:(rename H4' into H4).
          ltac1:(pose proof (compactify_by_vars_keeps_compactness _ _ _ _ _ H CompCBVA)).
          unfold is_compact_up_to_var in H6.
          specialize (H6 meqn meqn' H1 H2 H3).
          rewrite H5.
          assumption.
        }
        {
          apply H4' in H5.
          destruct H5.
        }
      }
    }
  }
}
Qed.

Lemma is_compact_up_to_vars_is_compact {Σ : StaticModel} {u_ops : U_ops} :
    ∀ (u : U), is_compact_up_to_vars u_ops u ∅ <-> is_compact u
.
Proof.
split.
{
  unfold is_compact_up_to_vars.
  unfold is_compact.
  setoid_rewrite difference_empty.
  intros.
  rewrite set_equiv.
  intros.
  split.
  {
    intros.
    rewrite elem_of_intersection in H3.
    destruct H3 as [H3 H4].
    ltac1:(pose proof (u_get_vars_exists_meqn u x) as T1).
    destruct T1 as [_ T1].
    rewrite Exists_exists in T1.
    ltac1:(pose proof T1 as H5).
    ltac1:(ospecialize (H5 _)).
    {
      exists meqn.
      apply (conj H0 H3).
    }
    clear T1.
    apply H in H5.
    unfold is_compact_up_to_var in H5.
    specialize (H5 meqn meqn' H0 H1 H2).
    destruct H5.
      {
        apply H5 in H3.
        destruct H3.
      }
      {
        apply H5 in H4.
        destruct H4.
      }
  }
  {
    intros.
    apply not_elem_of_empty in H3.
    destruct H3.
  }
}
{
  unfold is_compact_up_to_vars.
  unfold is_compact.
  setoid_rewrite difference_empty.
  unfold is_compact_up_to_var.
  intros.
  destruct (decide (v ∈ get_var_part meqn)) as [H4 | H4].
  {
    destruct (decide (v ∈ get_var_part meqn')) as [H5 | H5].
    {
      specialize (H meqn meqn' H1 H2 H3).
      rewrite set_equiv in H.
      specialize (H v).
      rewrite elem_of_intersection in H.
      ltac1:(pose proof (conj H4 H5)).
      rewrite H in H6.
      apply not_elem_of_empty in H6.
      destruct H6.
    }
    {
      right.
      assumption.
    }
  }
  {
    left.
    assumption.
  }
}
Qed.

Lemma compactify_by_vars_keeps_get_vars {Σ : StaticModel} {u_ops : U_ops}:
  ∀ (u u' : U) (lv : list variable), compactify_by_vars u_ops u lv = u' ->
  ∀ (v : variable), v ∈ u_get_vars u <-> v ∈ u_get_vars u'
.
Proof.
intros u u' lv.
revert u u'.
induction lv.
{
  intros.
  unfold compactify_by_vars in H.
  rewrite H.
  reflexivity.
}
{
  split.
  {
    intros.
    rewrite compactify_by_vars_inv_fold in H.
    remember (compactify_by_var u_ops u a) as CBVA.
    symmetry in HeqCBVA.
    specialize (IHlv CBVA u' H v).
    rewrite (compactify_by_var_keeps_get_vars _ _ _ _ HeqCBVA v) in H0.
    rewrite IHlv in H0.
    assumption.
  }
  {
    intros.
    rewrite compactify_by_vars_inv_fold in H.
    remember (compactify_by_var u_ops u a) as CBVA.
    symmetry in HeqCBVA.
    specialize (IHlv CBVA u' H v).
    rewrite (compactify_by_var_keeps_get_vars _ _ _ _ HeqCBVA v).
    rewrite IHlv.
    assumption.
  }
}
Qed.

Lemma compactify_by_vars_keeps_u_valid {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (lv : list variable), compactify_by_vars u_ops u lv = u' -> u_valid u -> u_valid u'
.
Proof.
intros u u' lv.
revert u u'.
induction lv.
{
  intros.
  unfold compactify_by_vars in H.
  rewrite H in H0.
  assumption.
}
{
  intros.
  rewrite compactify_by_vars_inv_fold in H.
  remember (compactify_by_var u_ops u a) as CBVA.
  symmetry in HeqCBVA.
  ltac1:(pose proof (compactify_by_var_keeps_u_valid _ _ _ HeqCBVA H0)).
  specialize (IHlv CBVA u' H H1).
  assumption.
}
Qed.

Lemma compactify_by_vars_keep_unifier_of {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U) (lv : list variable), compactify_by_vars u_ops u lv = u' ->
  u_valid u ->
  ∀ (s : SubTMM), is_unifier_of s (elements (up_of_u u)) <-> is_unifier_of s (elements (up_of_u u'))
.
Proof.
intros u u' lv.
revert u u'.
induction lv.
{
  intros.
  unfold compactify_by_vars in H.
  rewrite H.
  reflexivity.
}
{
  intros.
  rewrite compactify_by_vars_inv_fold in H.
  remember (compactify_by_var u_ops u a) as CBVA.
  symmetry in HeqCBVA.
  ltac1:(pose proof (compactify_by_var_keeps_u_valid _ _ _ HeqCBVA H0)).
  specialize (IHlv CBVA u' H H1 s).
  ltac1:(pose proof (compcatify_by_var_keeps_unifier_of _ _ _ HeqCBVA H0 s)).
  rewrite <- H2 in IHlv.
  assumption.
}
Qed.

Lemma compactify_is_compact {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U), compactify u = u' -> is_compact u'
.
Proof.
intros.
rewrite <- is_compact_up_to_vars_is_compact.
unfold compactify in H.
ltac1:(pose proof H as H').
apply compactify_by_vars_is_compact_up_to_vars in H.
assert (u_get_vars u' ∖ list_to_set ((elements ∘ u_get_vars) u) ≡ ∅).
{
  rewrite set_equiv.
  split.
  {
    intros.
    rewrite elem_of_difference in H0.
    destruct H0 as [H0 H1].
    rewrite elem_of_list_to_set in H1.
    unfold not in H1.
    rewrite <- (compactify_by_vars_keeps_get_vars _ _ _ H' x) in H0.
    rewrite <- elem_of_elements in H0.
    unfold compose in H1.
    apply H1 in H0.
    destruct H0.
  }
  {
    intros.
    apply not_elem_of_empty in H0.
    destruct H0.
  }
}
unfold is_compact_up_to_vars in *.
setoid_rewrite H0 in H.
assumption.
Qed.

Lemma compactify_keeps_valid_u {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U), compactify u = u' -> u_valid u -> u_valid u'
.
Proof.
intros.
unfold compactify in H.
apply (compactify_by_vars_keeps_u_valid _ _ _ H H0).
Qed.

Lemma compactify_keeps_equiv_UP {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u u' : U), compactify u = u' -> u_valid u -> (up_of_u u) ~up (up_of_u u')
.
Proof.
intros.
unfold equiv_UP.
unfold compactify in H.
ltac1:(pose proof (compactify_by_vars_keep_unifier_of _ _ _ H H0)).
assumption.
Qed.

(* Source of zipWith and transpose: https://gist.github.com/Agnishom/d686ef345d7c7b408362e1d2c9c64581#file-awesomelistlemmas-v
  this repo should contain relevant proofs for them *)

Definition zipWith {X Y Z} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
  map (fun '(x, y) => f x y) (combine xs ys)
.

Fixpoint transpose {X : Type} (len : nat) (tapes : list (list X)) : list (list X) :=
  match tapes with
    | [] => repeat [] len
    | t :: ts => zipWith cons t (transpose len ts)
  end
.


Definition term_has_same_symbol {Σ : StaticModel} (orig : TermOver BuiltinOrVar) (t : TermOver BuiltinOrVar) : bool :=
  match orig, t with
    | t_over (bov_builtin a), t_over (bov_builtin b) => bool_decide (a = b)
    | t_term a _, t_term b _ => bool_decide (a = b)
    | _, _ => false
  end
.

Definition dec_make_multeq {Σ : StaticModel} (lv : list (TermOver BuiltinOrVar)) (ln : list (TermOver BuiltinOrVar)) : option Meqn :=
  list_collect (var_term_to_var <$> lv) ≫= fun lv' => Some (list_to_set lv', ln)
.

Fixpoint dec_aux {Σ : StaticModel} (m : list (TermOver BuiltinOrVar)) (n : nat) : option (TermOver BuiltinOrVar * listset Meqn)%type :=
  match n with
    | O => None
    | S n => 
      let '(t_vars, t_nonvars) := partition (fun x => bool_decide (term_is_var x)) m in
        match head t_vars with
          | None =>
            match m with
              | [] => None
              | t :: _ => if bool_decide (Forall (term_has_same_symbol t) m)
              then
                match t with
                  | t_over _ => Some (t, empty)
                  | t_term s _ =>
                      term_args ← mapM term_params m;
                      ithMs ← Some (transpose (length term_args) term_args);
                      ithMsDeced ← (mapM (λ x, dec_aux x n) ithMs);
                      '(miCParams, miFrontEqs) ← Some (split ithMsDeced);
                      Some (t_term s miCParams, ⋃ miFrontEqs)
                end
              else None
            end
          | Some v => dec_make_multeq t_vars t_nonvars ≫= fun meqn => Some (v, singleton meqn)
        end
  end
.

Definition dec {Σ : StaticModel} (m : list (TermOver BuiltinOrVar)) : option (TermOver BuiltinOrVar * listset Meqn)%type :=
  dec_aux m (sum_list_with TermOver_size m)
.

Definition T {Σ : StaticModel} : Type :=
  list Meqn
.

Definition t_meqn_m_valid {Σ : StaticModel} (t : T) : Prop :=
  ∀ (meqn : Meqn), meqn ∈ t -> 1 >= length (get_nonvar_part meqn)
.

Definition t_meqn_v_prec {Σ : StaticModel} (t_car : list Meqn) : Prop :=
  ∀ (pred succ : list Meqn) (meqn : Meqn) (v : variable), 
    t_car = pred ++ (meqn :: succ) ->
    v ∈ get_var_part meqn ->
    v ∉ get_vars_of_nonvar_part_list_meqns succ
.

Definition t_valid {Σ : StaticModel} (t : T) : Prop :=
  t_meqn_m_valid t ∧ t_meqn_v_prec t ∧ Forall meqn_valid t
.

Definition up_of_t {Σ : StaticModel} (t : T) : UP :=
  up_of_list t
.

Definition R {Σ : StaticModel} {u_ops : U_ops} : Type :=
  (T * U)%type
.

Instance r_elements {Σ : StaticModel} {u_ops : U_ops} : Elements Meqn R :=
  λ '(t, u), t ++ elements u
.

Instance r_elem_of {Σ : StaticModel} {u_ops : U_ops} : ElemOf Meqn R :=
  λ meqn r, meqn ∈ elements r
.

Definition up_of_r {Σ : StaticModel} {u_ops : U_ops} (r : R) : UP :=
  let '(t, u) := r in
    up_of_t t ∪ up_of_u u
.

Definition r_vars_disjoint {Σ : StaticModel} {u_ops : U_ops} (r : R) : Prop :=
    ∀ (meqn meqn' : Meqn),
      meqn ∈ r ->
      meqn' ∈ r ->
      get_var_part meqn ∩ get_var_part meqn' = ∅
.

Definition r_has_all_vars {Σ : StaticModel} {u_ops : U_ops} (r : R) : Prop :=
  get_vars_of_var_part_list_meqns (elements r) = get_vars_of_nonvar_part_list_meqns (elements r)
.

Definition r_valid {Σ : StaticModel} {u_ops : U_ops} (r : R) : Prop :=
  let '(t, u) := r in
    t_valid t ∧ u_valid u ∧ r_vars_disjoint r ∧ r_has_all_vars r
.

Fixpoint u_insert_many {Σ : StaticModel} {u_ops : U_ops} (u : U) (lm : list Meqn) : U :=
  match lm with
    | [] => u
    | x::xs => u_insert_many (u_insert u x) xs
  end
.

Definition init_r {Σ : StaticModel} {u_ops : U_ops} (t : TermOver BuiltinOrVar) (t' : TermOver BuiltinOrVar) : R :=
  let vars : list variable := elements ((vars_of t) ∩ (vars_of t')) in
  let meqns : list Meqn := (λ v, init_meqn (singleton v) []) <$> vars in
  let u_empty : U := empty in
  let u_missing_up : U := u_insert_many u_empty meqns in
  let up_meqn : Meqn := init_meqn (singleton (fresh vars)) [t;t'] in
    ([], u_insert u_missing_up up_meqn)
.

Lemma init_r_valid {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (t t' : TermOver BuiltinOrVar) (r : R), init_r t t' = r -> r_valid r
.
Proof.
Abort.


Definition u_subst {Σ : StaticModel} {u_ops : U_ops} (u : U) (sub : SubTMM) : U :=
  u_map u (λ meqn, meqn_subst meqn sub)
.

Fixpoint unify_r_aux {Σ : StaticModel} {u_ops : U_ops} (r : R) (n : nat) : option (list Meqn) :=
  match n with
    | O => None
    | S n =>
      let '(t, u) := r in
        match elements u with
          | [] => Some (reverse t)
          | _ => match u_extract_nonempty_m_meqn u with
                  | None => Some (reverse t ++ elements u)
                  | Some ((s, m), u_rest) => 
                        '(common_part, frontier) ← dec m;
                        let frontier_l := elements frontier in
                          if existsb (meqns_s_intersect (s, m)) frontier_l then None
                          else
                              let sub : SubTMM := gset_to_gmap common_part s in
                              let u_meqn_reduced := u_insert_many u_rest frontier_l in
                              let u_compactified := compactify u_meqn_reduced in
                                  unify_r_aux ((meqn_subst (init_meqn s [common_part]) sub)::t, u_subst u_compactified sub) n
                end
        end
  end
.

Lemma unify_r_aux_n_enough {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u : U) (t t' : T), r_valid (t, u) ->
    unify_r_aux (t, u) (length (elements u) + 1) = Some t' <-> ∃ (sub : SubTMM), is_unifier_of sub (elements (up_of_r (t, u)))
.
Proof.
Abort.

Lemma unify_r_aux_valid_t {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (u : U) (t t' : T), r_valid (t, u) ->
  unify_r_aux (t, u) (length (elements u) + 1) = Some t' -> t_valid t'
.
Proof.
Abort.

Definition unify_r {Σ : StaticModel} {u_ops : U_ops} (r : R) :=
  let '(t, u) := r in
  let u_len := length (elements u) in
    unify_r_aux r (u_len + 1)
.

Definition unify_terms {Σ : StaticModel} {u_ops : U_ops} (t : TermOver BuiltinOrVar) (t' : TermOver BuiltinOrVar) : option (list Meqn) :=
  unify_r (init_r t t')
.

Fixpoint extract_mgu_aux {Σ : StaticModel} (t : T) (sub : SubTMM) : SubTMM :=
  match t with
    | [] => sub
    | ((s, m)::xs) => 
      let '(_, m_sub) := meqn_subst (s, m) sub in
        match head m_sub with
          | None => extract_mgu_aux xs sub
          | Some x =>
            let new_sub := gset_to_gmap x s in
              extract_mgu_aux xs new_sub
        end
  end
.

Definition extract_mgu {Σ : StaticModel} (t : T) : SubTMM :=
  extract_mgu_aux (reverse t) empty
.

Lemma sub_is_unifier {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (t t' : TermOver BuiltinOrVar) (r_t : T),
    unify_terms t t' = Some r_t ->
    sub_app_mm (extract_mgu r_t) t = sub_app_mm (extract_mgu r_t) t'
.
Proof.
Abort.

Lemma sub_no_unifier {Σ : StaticModel} {u_ops : U_ops} :
  ∀ (t t' : TermOver BuiltinOrVar),
    unify_terms t t' = None ->
    ∀ (sub : SubTMM), sub_app_mm sub t ≠ sub_app_mm sub t'
.
Proof.
Abort.
