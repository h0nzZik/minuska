
From Minuska Require Import
    prelude
    spec
    naive_interpreter
.

Fixpoint interp_loop
    {Σ : BackgroundModel}
    (nvs : nat -> NondetValue)
    (idx : nat)
    (interp : NondetValue -> TermOver BasicValue -> option (TermOver BasicValue))
    (fuel : nat)
    (g : TermOver BasicValue)
    : (nat*(TermOver BasicValue))
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
    {Σ : BackgroundModel}
    (nvs : nat -> NondetValue)
    (idx : nat)
    (interp : NondetValue -> (TermOver BasicValue)*hidden_data -> option ((TermOver BasicValue)*hidden_data*nat))
    (fuel : nat)
    (g : (TermOver BasicValue)*hidden_data)
    (log : list nat)
    : (nat*(TermOver BasicValue)*hidden_data*(list nat))
:=
match fuel with
| 0 => (0,g.1,g.2,log)
| S fuel' =>
    match interp (nvs idx) g with
    | None => (fuel', g.1, g.2, log)
    | Some (g',log_entry) => interp_loop_ext nvs (S idx) interp fuel' g' (cons log_entry log)
    end
end
.

Definition interp_in_from'
        {Σ : BackgroundModel}
        {Label : Set}
        (Γ : (list (RewritingRule2 Label))*(list string))
        (program : ProgramT)
        (nvs : nat -> NondetValue)
        (fuel : nat)
        (from : (TermOver BasicValue)*hidden_data)
        :  nat * (TermOver BasicValue) * hidden_data * list (option string)
    :=
        let res := interp_loop_ext nvs 0 (naive_interpreter_ext Γ.1 program)
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
        {Σ : BackgroundModel}
        {Label : Set}
        (program : ProgramT)
        (Γ : (list (RewritingRule2 Label))*(list string))
        (nvs : nat -> NondetValue)
        (fuel : nat)
        (from : (TermOver BasicValue)*hidden_data)
        :  nat * (TermOver BasicValue)*hidden_data * string
:=
    let r := interp_in_from' Γ program nvs fuel from in
    (r.1, concat_list_option_str r.2)
.
