From Minuska Require Import
  prelude
  spec
  basic_properties
.

Fixpoint count_occ
  {A B : Type}
  (i : nat)
  (p : nat -> @TermOver' A B -> bool)
  (t : @TermOver' A B)
  : nat
:=
  if (p i t) then 1 else (
    match t with
    | t_over _ => 0
    | t_term s l => (
        fix go (i' : nat) (l' : list (@TermOver' A B)) : nat :=
        match l' with
        | [] => 0
        | x::xs =>
            let n := count_occ i' p x in
            n + (go (i' + n) xs)
        end
      ) i l
    end
  )
.


Fixpoint term_map'
  {A B : Type}
  (i : nat)
  (p : nat -> @TermOver' A B -> bool)
  (f : nat -> option (@TermOver' A B))
  (t : @TermOver' A B)
  : @TermOver' A B
:=
  if (p i t) then (
    match (f i) with
    | None => t
    | Some t' => t'
    end
  ) else (
  match t with
  | t_over _ => t
  | t_term s l =>
      let l' := (
        fix go (l' : list (@TermOver' A B)) (i' : nat) : list (@TermOver' A B) :=
          match l' with
          | [] => []
          | x::xs =>
              let x' := term_map' i' p f x in
              let i'' := i' + count_occ i' p x in
              let xs' := go xs i'' in
              (x' :: xs')
          end
      ) l i in
      t_term s l'
  end)
.

Definition term_map
  {A B : Type}
  (p : nat -> @TermOver' A B -> bool)
  (f : nat -> option (@TermOver' A B))
  (t : @TermOver' A B)
  : @TermOver' A B
:=
  term_map' 0 p f t
.

Definition PatchT {A B : Type} : Type := list ((@TermOver' A B)*(@TermOver' A B)).

Definition apply_patch
  {A B : Type}
  {_EA : EqDecision A}
  {_EB : EqDecision B}
  (p : PatchT)
  (t0 : @TermOver' A B)
  : @TermOver' A B
:=
  term_map
    (fun i t => match (p !! i) with None => false | Some x => bool_decide (x.1 = t) end)
    (fun i => fmap snd (p !! i) )
    t0
.

Fixpoint count_symbol_occ
  {A B : Type}
  {_EA : EqDecision A}
  (a : A)
  (t : @TermOver' A B)
  : nat
:=
  match t with
  | t_over _ => 0
  | t_term s l =>
      let n1 := if (decide (s = a)) then 1 else 0 in
      let n2 := sum_list_with (count_symbol_occ a) l in
      n1 + n2
  end
.

(*
  We need to transform a language definition such that it operates on programs
  where one particular language construct (`a`) takes one more extra parameter
  that gets preserved. This parameter would typically be a natural number,
  and would be unique across the whole program, so that we can trace which
  syntactic element introduced the 'current' term when firing a rule.
 *)
Fixpoint more_space_for_symbol_in_term
  {A B : Type}
  {_EA : EqDecision A}
  (a : A)
  (i : nat)
  (genb : nat -> B)
  (t : @TermOver' A B)
  : @TermOver' A B
:=
  match t with
  | t_over x => t_over x
  | t_term a' l =>
      let go := (fix go (l : list (@TermOver' A B)) (i' : nat) : list (@TermOver' A B) :=
          match l with
          | [] => []
          | x::xs =>
              let x' := more_space_for_symbol_in_term a i' genb x in
              let xs' := go xs (i' + count_symbol_occ a x) in
              x'::xs'
          end
      ) in
      if (decide (a = a')) then (
        let i' := (S i) in
        let l' := go l i' in
        t_term a' ((t_over (genb i))::l')
      )
      else (
        t_term a' (go l i)
      )
  end
.
