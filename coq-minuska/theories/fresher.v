From Minuska Require Import
    prelude
    spec
.

Record FresherR {Σ : BackgroundModel} := {
    fresher_avoid : list Variabl ;
}.

Definition FresherM {Σ : BackgroundModel} (A : Type) : Type :=
    FresherR -> (A*FresherR)%type
.

(* Definition fresherOf {Σ : BackgroundModel} (avoid : list Variabl)
    : FresherM ()
:=
    fun _ => ((), {|fresher_avoid := avoid|})
. *)

Definition returnFresher {Σ : BackgroundModel}
    {A : Type}
    (a : A)
    :
    FresherM A
:=
    fun F => (a, F)
.


Definition fmapFresher
    {Σ : BackgroundModel}
    {A B : Type}
    (f : A -> B)
    (v : FresherM A)
    : FresherM B
:=
    fun F =>
    (f (v F).1, (v F).2)
.


Definition bindFresher
    {Σ : BackgroundModel}
    {A B : Type}
    (v : FresherM A)
    (f : A -> FresherM B)
    : FresherM B
:=
    fun F =>
    f (v F).1 F
.


Definition freshFresher
    {Σ : BackgroundModel}
    {A : Type}
    (f : Variabl -> A)
    : FresherM A
:=
    fun F =>
    let x := fresh (F.(fresher_avoid)) in
    let xs := x::(F.(fresher_avoid)) in
    (f x, {|fresher_avoid:=xs;|})
.




