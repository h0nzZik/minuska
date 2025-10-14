From Minuska Require Import
  prelude
  spec
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
