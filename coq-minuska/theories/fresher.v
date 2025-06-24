From Minuska Require Import
    prelude
    spec
.

Record FresherR {Σ : StaticModel} := {
    fresher_avoid : list variable ;
}.

Definition FresherM {Σ : StaticModel} (A : Type) : Type :=
    FresherR -> (A*FresherR)%type
.

(* Definition fresherOf {Σ : StaticModel} (avoid : list variable)
    : FresherM ()
:=
    fun _ => ((), {|fresher_avoid := avoid|})
. *)

Definition returnFresher {Σ : StaticModel}
    {A : Type}
    (a : A)
    :
    FresherM A
:=
    fun F => (a, F)
.


Definition fmapFresher
    {Σ : StaticModel}
    {A B : Type}
    (f : A -> B)
    (v : FresherM A)
    : FresherM B
:=
    fun F =>
    (f (v F).1, (v F).2)
.


Definition bindFresher
    {Σ : StaticModel}
    {A B : Type}
    (v : FresherM A)
    (f : A -> FresherM B)
    : FresherM B
:=
    fun F =>
    f (v F).1 F
.


Definition freshFresher
    {Σ : StaticModel}
    {A : Type}
    (f : variable -> A)
    : FresherM A
:=
    fun F =>
    let x := fresh (F.(fresher_avoid)) in
    let xs := x::(F.(fresher_avoid)) in
    (f x, {|fresher_avoid:=xs;|})
.




