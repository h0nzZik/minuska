
From Minuska Require Import
    prelude
    spec
    naive_interpreter
.

Fixpoint interp_loop
    {Σ : StaticModel}
    (nvs : nat -> NondetValue)
    (idx : nat)
    (interp : NondetValue -> TermOver builtin_value -> option (TermOver builtin_value))
    (fuel : nat)
    (g : TermOver builtin_value)
    : (nat*(TermOver builtin_value))
:=
match fuel with
| 0 => (0,g)
| S fuel' =>
    match interp (nvs idx) g with
    | None => (fuel', g)
    | Some g' => interp_loop nvs (S idx) interp fuel' g'
    end
end
.

Fixpoint interp_loop_ext
    {Σ : StaticModel}
    (nvs : nat -> NondetValue)
    (idx : nat)
    (interp : NondetValue -> (TermOver builtin_value) -> option ((TermOver builtin_value)*nat))
    (fuel : nat)
    (g : (TermOver builtin_value))
    (log : list nat)
    : (nat*(TermOver builtin_value)*(list nat))
:=
match fuel with
| 0 => (0,g,log)
| S fuel' =>
    match interp (nvs idx) g with
    | None => (fuel', g, log)
    | Some (g',log_entry) => interp_loop_ext nvs (S idx) interp fuel' g' (cons log_entry log)
    end
end
.

Definition interp_in_from'
        {Σ : StaticModel}
        {Act : Set}
        (Γ : (list (RewritingRule2 Act))*(list string))
        (nvs : nat -> NondetValue)
        (fuel : nat)
        (from : (TermOver builtin_value))
        :  nat * (TermOver builtin_value) * list (option string)
    :=
        let res := interp_loop_ext nvs 0 (naive_interpreter_ext Γ.1)
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
        {Act : Set}
        (Γ : (list (RewritingRule2 Act))*(list string))
        (nvs : nat -> NondetValue)
        (fuel : nat)
        (from : (TermOver builtin_value))
        :  nat * (TermOver builtin_value) * string
:=
    let r := interp_in_from' Γ nvs fuel from in
    (r.1, concat_list_option_str r.2)
.
