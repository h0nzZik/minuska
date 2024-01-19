
From Minuska Require Import
    prelude
    spec_syntax
    flattened
    naive_interpreter
.

Fixpoint interp_loop
    {Σ : StaticModel}
    (interp : GroundTerm -> option GroundTerm)
    (fuel : nat)
    (g : GroundTerm)
    : (nat*GroundTerm)
:=
match fuel with
| 0 => (0,g)
| S fuel' =>
    match interp g with
    | None => (fuel', g)
    | Some g' => interp_loop interp fuel' g'
    end
end
.

Fixpoint interp_loop_ext
    {Σ : StaticModel}
    (interp : GroundTerm -> option (GroundTerm*nat))
    (fuel : nat)
    (g : GroundTerm)
    (log : list nat)
    : (nat*GroundTerm*(list nat))
:=
match fuel with
| 0 => (0,g,log)
| S fuel' =>
    match interp g with
    | None => (fuel', g, log)
    | Some (g',log_entry) => interp_loop_ext interp fuel' g' (cons log_entry log)
    end
end
.

Definition interp_in_from'
        {Σ : StaticModel}
        (Γ : (FlattenedRewritingTheory)*(list string))
        (fuel : nat)
        (from : GroundTerm)
        :  nat * GroundTerm * list (option string)
    :=
        let res := interp_loop_ext (naive_interpreter_ext Γ.1)
            fuel
            from
            nil
        in
        (res.1, (fun n => Γ.2 !! n) <$> (reverse res.2))
    .

Definition concat_list_option_str
    (l: list (option string))
    : string
:=
    fold_left (fun a ob =>
        let s := match ob with
        | None => "?"
        | Some b => b
        end in
        a +:+ ", " +:+ s
    ) l ""
.

Definition interp_in_from
        {Σ : StaticModel}
        (Γ : (FlattenedRewritingTheory)*(list string))
        (fuel : nat)
        (from : GroundTerm)
        :  nat * GroundTerm * string
:=
    let r := interp_in_from' Γ fuel from in
    (r.1, concat_list_option_str r.2)
.
