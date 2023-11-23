From Minuska Require Import
    prelude
.

Section sec_graph.

Context
  `(R : relation T)
  `{!RelDecision R}
  `{FinSet T TSet}
  `{RelDecision T TSet elem_of}
  .

Section sec_dfs.

Context
  (nodes : list T)
  .

Definition one_step_reachable (x : T) : list T :=
  filter (fun y => R x y) nodes.

Inductive find_cycle_result : Type :=
| has_cycle (c : list T)
| reaches (r : TSet).

Section sec_take_until.

Context
  (P : T -> Prop)
  `{forall x, Decision (P x)}
  .

Fixpoint take_until (l : list T) : list T :=
  match l with
  | [] => []
  | x :: t =>x ::
    if (decide (P x)) then [] else take_until t
  end. 

Lemma take_until_is_take (l : list T) :
  exists n, take_until l = take n l.
Proof.
  induction l.
  - exists 0; reflexivity.
  - cbn; ltac1: (case_decide).
    + exists 1; reflexivity.
    + destruct IHl as [n ->].
      exists (S n); reflexivity.
Qed.

Lemma take_until_subseteq (l : list T) :
  take_until l ⊆ l.
Proof.
  destruct (take_until_is_take l) as [n ->].
  apply subseteq_take.
Qed.

Lemma take_until_prefix (l : list T) :
  take_until l `prefix_of` l.
Proof.
  destruct (take_until_is_take l) as [n ->].
  apply prefix_take.
Qed.

End sec_take_until.

Lemma find_cycle_obligation_helper :
  forall (explore path : list T) (x : T),
  lexprod nat nat lt lt
  (size
    ((list_to_set (C := TSet) nodes
      ∪
      list_to_set explore)
      ∖
      list_to_set path),
   length explore)
  (size
    ((list_to_set (C := TSet) nodes
      ∪
      ({[x]} ∪ list_to_set explore))
      ∖ list_to_set path),
   S (length explore)).
Proof.
intros.
remember (size _) as size1.
remember (size ((_ ∪ (_ ∪ _)) ∖ _)) as size2.
destruct (decide (size1 = size2)) as [-> |].
  + ltac1 : (apply right_lex; lia).
  + apply left_lex.
    ltac1: (cut (size1 <= size2); [lia |]).
    subst; apply subseteq_size; intro y.
    ltac1: (rewrite !elem_of_difference).
    intros []; split.
    * ltac1: (set_solver).
    * assumption.
Qed.

Equations? find_cycle (explore path : list T) (explored : TSet) : find_cycle_result
  by wf (size ((list_to_set (C := TSet) nodes ∪ list_to_set explore) ∖ list_to_set path), length explore) :=
find_cycle [] _ _ := reaches explored;
find_cycle (x :: explore) path explored
with (decide (x ∉ nodes)) => {
| left _ => find_cycle explore path explored;
| right _
  with (decide (x ∈ explored ∪ list_to_set path)) => {
  | left _ => find_cycle explore path explored;
  | right _
    with inspect (one_step_reachable x) => {
    | exist _ x_next _
      with inspect (filter (fun x => x ∈ path) x_next) => {
      | exist _ (y :: _) _ => has_cycle (rev (x :: take_until (fun z => z = y) path));
      | exist _ [] _
        with find_cycle x_next (x :: path) explored => {
        | has_cycle c => has_cycle c;
        | reaches expl => find_cycle explore path ({[x]} ∪ expl ∪ explored)
        }
      }
    }
  }
}.
Proof.
- apply find_cycle_obligation_helper.
- apply find_cycle_obligation_helper.
- apply left_lex.
  assert (Hrew :
    list_to_set (C := TSet) nodes ∪ list_to_set (one_step_reachable x)
      ≡ list_to_set nodes).
  {
    unfold one_step_reachable; intro y; rewrite elem_of_union.
    ltac1: (rewrite !elem_of_list_to_set; rewrite elem_of_list_filter).
    ltac1: (set_solver).
  }
  rewrite Hrew.
  apply subset_size.
  split.
  + intro y.
    ltac1: (rewrite !elem_of_difference; set_solver).
  + intros Hsub.
    specialize (Hsub x).
    ltac1: (rewrite !elem_of_difference in Hsub).
    ltac1: (rewrite !elem_of_union in Hsub).
    ltac1: (rewrite !elem_of_list_to_set in Hsub).
    ltac1: (set_solver).
- apply find_cycle_obligation_helper.
Qed.

Definition graph_find_cycle : find_cycle_result :=
  find_cycle nodes [] ∅.

End sec_dfs.

Inductive graph_walk_from_to : T -> T -> list T -> Prop :=
| gw_empty : forall (x : T), graph_walk_from_to x x []
| gw_cons : forall (x x' y : T) (l : list T),
    R x x' -> graph_walk_from_to x' y l -> graph_walk_from_to x y (x' :: l)
.

Lemma graph_walk_from_to_last (x y : T) (w : list T) :
  graph_walk_from_to x y w -> w <> [] -> list.last w = Some y.
Proof.
  intros Hwalk Hnil.
  induction Hwalk.
  - ltac1:(by contradict Hnil).
  - inversion Hwalk; subst.
    + ltac1:(done).
    + ltac1: (by apply IHHwalk).
Qed.

Inductive graph_walk : list T -> Prop :=
| gw : forall (x : T) (w : list T),
    graph_walk_from_to x (last w x) w -> graph_walk (x :: w).

Record graph_path_from_to (x y : T) (w : list T) : Prop :=
{
    gp_walk : graph_walk_from_to x y w;
    gp_nodup : NoDup (x :: w);
}.

Inductive graph_path : list T -> Prop :=
| gp : forall (x : T) (w : list T),
    graph_path_from_to x (last w x) w -> graph_path (x :: w).

Record graph_cycle_from_to (x y : T) (w : list T) : Prop :=
{
    gc_path : graph_path_from_to x y w;
    gc_closed : R y x;
}.

Inductive graph_cycle : list T -> Prop :=
| gc : forall (x : T) (w : list T),
    graph_cycle_from_to x (last w x) w ->
    graph_cycle (x :: w).

Record graph_contains_cycle_witness (nodes c : list T) : Prop :=
{
    gccw_subset : c ⊆ nodes;
    gccw_cycle : graph_cycle c;
}.

Lemma graph_find_cycle_sound (nodes c : list T) :
  graph_find_cycle nodes = has_cycle c ->
  graph_contains_cycle_witness nodes c.
Proof.
  unfold graph_find_cycle; intros Heq.
  remember nodes as explore.
  rewrite Heqexplore in Heq at 1.
  rewrite Heqexplore.
  assert (Hsub : explore ⊆ nodes) by (subst; reflexivity).
  clear Heqexplore.
  remember ∅ as explored; clear Heqexplored.
  remember [] as path.
  assert (Hpath : Forall (fun x => graph_path (rev (x :: path))) explore).
  {
    apply list.Forall_forall; intros x Hx; subst; cbn.
    repeat constructor.
    apply not_elem_of_nil.
  }
  assert (Hpath_sub : path ⊆ nodes) by ltac1: (subst; set_solver).
  clear Heqpath.
  ltac1: (funelim (find_cycle nodes explore path explored)).
  - ltac1: (congruence).
  - apply H8.
    + rewrite Heqcall; assumption.
    + ltac1: (set_solver).
    + inversion Hpath; assumption.
    + assumption.
  - apply H8.
    + rewrite Heqcall; assumption.
    + ltac1: (set_solver).
    + inversion Hpath; assumption.
    + assumption.
  - rewrite <- Heqcall in Heq1.
    inversion Heq1; subst.
    inversion Hpath; subst.
    split.
    + 
Admitted.

Definition is_reachable_from
    (from to : T)
:=
    ∃ l, graph_path_from_to from to l
.

Definition is_reachable_from_nodes
    (nodes : list T)
    (to : T)
:=
    Exists (fun from => is_reachable_from from to) nodes
.

Definition all_are_reachable_from_nodes
    (nodes : list T)
    (targets : list T)
:=
    Forall (fun to => is_reachable_from_nodes nodes to) targets
.

Theorem has_a_cycle_dec
    `{EqDecision T}
    `{!RelDecision R}
    (nodes : list T)
    : Decision (has_a_cycle_over nodes)
.
Proof.
    (* TODO *)
Abort.

Theorem all_are_reachable_from_nodes_dec
    `{EqDecision T}
    (nodes : list T)
    (targets : list T)
    : Decision (all_are_reachable_from_nodes nodes targets)
.
Proof.
    (* TODO *)
Abort.