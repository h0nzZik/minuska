From Coq.Logic Require Import ProofIrrelevance.


From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    builtins
    flattened
    naive_interpreter
    default_static_model
    notations
    frontend
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

Module example_1.

    #[local]
    Instance Σ : StaticModel :=
        default_model (default_builtin.β)
    .
    
    Definition X : variable := "X".

    Definition cfg {_br : BasicResolver} := (apply_symbol "cfg").
    Arguments cfg {_br} _%rs.

    Definition s {_br : BasicResolver} := (apply_symbol "s").
    Arguments s {_br} _%rs.

    Definition Decls : list Declaration := [
        decl_rule (
            rule ["my_rule"]:
                cfg [ s [ s [ ($X) ] ] ]
                ~> cfg [ $X ]
        )
    ].

    Definition Γ : FlattenedRewritingTheory*(list string)
        := Eval vm_compute in (to_theory (process_declarations (Decls))).

    Definition interp :=
        naive_interpreter Γ.1
    .

    (* TODO remove *)
    Fixpoint interp_loop
        (fuel : nat)
        (g : GroundTerm)
        : (nat*GroundTerm)
    :=
    match fuel with
    | 0 => (0,g)
    | S fuel' =>
        match interp g with
        | None => (fuel', g)
        | Some g' => interp_loop fuel' g'
        end
    end
    .

    Fixpoint my_number' (n : nat) : AppliedOperator' symbol builtin_value  :=
    match n with
    | 0 => ao_operator "0"
    | S n' => ao_app_ao (ao_operator "s") (my_number' n')
    end
    .

    Fixpoint my_number'_inv
        (g : AppliedOperator' symbol builtin_value)
        : option nat
    :=
    match g with
    | ao_operator s => if bool_decide (s = "0") then Some 0 else None
    | ao_app_ao s arg =>
        match s with
        | ao_operator s => if bool_decide (s = "s") then
            n ← my_number'_inv arg;
            Some (S n)
        else None
        | _ => None
        end
    | ao_app_operand _ _ => None
    end
    .

    Definition my_number (n : nat) : GroundTerm :=
        aoo_app (ao_app_ao (ao_operator "cfg") (my_number' n))
    .

    Definition my_number_inv (g : GroundTerm) : option nat
    :=
    match g with
    | aoo_app (ao_app_ao (ao_operator "cfg") g') => my_number'_inv g'
    | _ => None
    end
    .

    Lemma my_number_inversion' : forall n,
        my_number'_inv (my_number' n) = Some n
    .
    Proof.
        induction n; simpl.
        { reflexivity. }
        {
            rewrite bind_Some.
            exists n.
            auto.
        }
    Qed.

    Lemma my_number_inversion : forall n,
        my_number_inv (my_number n) = Some n
    .
    Proof.
        intros n. simpl. apply my_number_inversion'.
    Qed.

    Compute (my_number 2).
    Compute (interp (my_number 2)).

    Definition interp_loop_number fuel := 
        fun n =>
        let fg' := ((interp_loop fuel) ∘ my_number) n in
        my_number_inv fg'.2
    .

End example_1.


Module two_counters.

    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).


    Definition M : variable := "M".
    Definition N : variable := "N".
    
    Definition cfg {_br : BasicResolver} := (apply_symbol "cfg").
    Arguments cfg {_br} _%rs.

    Definition state {_br : BasicResolver} := (apply_symbol "state").
    Arguments state {_br} _%rs.

    Definition s {_br : BasicResolver} := (apply_symbol "s").
    Arguments s {_br} _%rs.

    Definition Γ : FlattenedRewritingTheory*(list string) :=
    Eval vm_compute in (to_theory (process_declarations ([
        decl_rule (
            rule ["my-rule"]:
                cfg [ state [ s [ $M ], $N ] ]
            ~> cfg [ state [ $M, s [ $N ]  ] ]
        )
    ]))).
    

    Definition interp :=
        naive_interpreter Γ.1
    .

    Definition pair_to_state (mn : nat*nat) : GroundTerm :=
        aoo_app (ao_app_ao (ao_operator "cfg")
        (
            ao_app_ao
                (
                ao_app_ao (ao_operator "state")
                    (example_1.my_number' mn.1)
                )
                (example_1.my_number' mn.2)
        )
        )
    .

    Definition state_to_pair (g : GroundTerm) : option (nat*nat) :=
    match g with
    | aoo_app (ao_app_ao (ao_operator "cfg")
        (ao_app_ao (ao_app_ao (ao_operator "state") (m')) n'))
        => 
            m ← example_1.my_number'_inv m';
            n ← example_1.my_number'_inv n';
            Some (m, n)
    | _ => None
    end
    .

    Lemma pair_state_inversion : forall m n,
        state_to_pair (pair_to_state (m,n)) = Some (m,n)
    .
    Proof.
        intros m n.
        simpl.
        rewrite bind_Some.
        exists m.
        split.
        { rewrite example_1.my_number_inversion'. reflexivity. }
        rewrite bind_Some.
        exists n.
        split.
        { rewrite example_1.my_number_inversion'. reflexivity. }
        reflexivity.
    Qed.

    Definition interp_loop_number fuel := 
        fun (m n : nat) =>
        let fg' := ((interp_loop interp fuel) ∘ pair_to_state) (m,n) in
        state_to_pair fg'.2
    .

    (* Time Compute (interp_loop_number 10000000 10000 10000). *)

End two_counters.

Module arith.

    Import default_builtin.
    Import default_builtin.Notations.

    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).

    Definition X : variable := "X".
    Definition Y : variable := "Y".
    Definition REST_SEQ : variable := "$REST_SEQ".
    
    Definition cseq {_br : BasicResolver} := (apply_symbol "cseq").
    Arguments cseq {_br} _%rs.

    Definition emptyCseq {_br : BasicResolver} := (apply_symbol "emptyCseq").
    Arguments emptyCseq {_br} _%rs.

    Definition plus {_br : BasicResolver} := (apply_symbol "plus").
    Arguments plus {_br} _%rs.

    Definition minus {_br : BasicResolver} := (apply_symbol "minus").
    Arguments minus {_br} _%rs.

    Definition times {_br : BasicResolver} := (apply_symbol "times").
    Arguments times {_br} _%rs.

    Definition div {_br : BasicResolver} := (apply_symbol "div").
    Arguments div {_br} _%rs.

    Definition cfg {_br : BasicResolver} := (apply_symbol "cfg").
    Arguments cfg {_br} _%rs.

    Definition state {_br : BasicResolver} := (apply_symbol "state").
    Arguments state {_br} _%rs.

    Definition s {_br : BasicResolver} := (apply_symbol "s").
    Arguments s {_br} _%rs.

    Definition freezer {_br : BasicResolver} (sym : symbol) (position : nat)
    :=
        (apply_symbol ("freezer_" +:+ sym +:+ "_" +:+ (pretty position)))
    .
    Arguments freezer {_br} _%rs.


    Declare Scope LangArithScope.
    Delimit Scope LangArithScope with larith.

    Notation "x '+' y" := (plus [ x, y ])%larith.
    Notation "x '-' y" := (minus [ x, y ])%larith.
    Notation "x '*' y" := (times [ x, y ])%larith.
    Notation "x '/' y" := (div [ x, y ])%larith.

    Open Scope larith.

    #[local]
    Instance ArithDefaults : Defaults := {|
        default_context_template
            := (context-template cfg [ HOLE ] with HOLE) ;

        default_isValue := fun x => (isNat x) ;
    |}.

    Definition Decls : list Declaration := [
        (* plus *)
        decl_rule (
            rule ["plus-nat-nat"]:
                cfg [ cseq [ ($X + $Y), $REST_SEQ ] ]
            ~> cfg [ cseq [ ($X +Nat $Y) , $REST_SEQ ] ]
                where (
                    (isNat ($X))
                    &&
                    (isNat ($Y))
                )
        );
        decl_strict (symbol "plus" of arity 2 strict in [0;1]);
        (* minus *)
        decl_rule (
            rule ["minus-nat-nat"]:
                cfg [ cseq [ ($X - $Y), $REST_SEQ ] ]
            ~> cfg [ cseq [ ($X -Nat $Y) , $REST_SEQ ] ]
                where (
                    (isNat ($X))
                    &&
                    (isNat ($Y))
                )
        );
        decl_strict (symbol "minus" of arity 2 strict in [0;1]);
        (* times *)
        decl_rule (
            rule ["times-nat-nat"]:
                cfg [ cseq [ (($X) * ($Y)), $REST_SEQ ] ]
            ~> cfg [ cseq [ ($X *Nat $Y) , $REST_SEQ ] ]
                where (
                    (isNat ($X))
                    &&
                    (isNat ($Y))
                )
        );
        decl_strict (symbol "times" of arity 2 strict in [0;1]);
        (* div *)
        decl_rule (
            rule ["div-nat-nat"]:
                cfg [ cseq [ (($X) / ($Y)), $REST_SEQ ] ]
            ~> cfg [ cseq [ ($X /Nat $Y) , $REST_SEQ ] ]
                where (
                    (isNat ($X))
                    &&
                    (isNat ($Y))
                )
        );
        decl_strict (symbol "div" of arity 2 strict in [0;1])
    ].

    Definition Γ : FlattenedRewritingTheory*(list string) := Eval vm_compute in 
    (to_theory (process_declarations (Decls))).


    (*
    Definition initial1 (x y : nat) :=
        (ground (cfg [ cseq [ ((@aoo_operand symbol _ (bv_nat x)) + (@aoo_operand symbol _ (bv_nat y))), emptyCseq [] ] ]))
    .*)

    Definition initial0 (x : AppliedOperatorOr' symbol builtin_value) :=
        (ground (
            cfg [
                cseq [ 
                    x,
                    emptyCseq []
                    ]
                ]
            )
        )
    .

    Definition initial (x: nat) (ly : list nat) :=
        (ground (initial0 ((foldr 
            (fun a (b : AppliedOperatorOr' symbol builtin_value) =>
                plus [((bv_nat a)) , b]
            )
            (@aoo_operand symbol builtin_value (bv_nat x))
            ly
        ))))
    .

    Definition interp_from (fuel : nat) from
        := interp_in_from Γ fuel from
    .

    Definition interp_list (fuel : nat) (x : nat) (ly : list nat)
    :=
        interp_from fuel (initial x ly)
    .
     
    (*
    (* Debugging notations *)
    Notation "( x ( y ) )" := (ao_app_ao x y) (only printing).
    Notation "( x ( y ) )" := (ao_app_operand x y) (only printing).
    Notation "( x )" := (ao_operator x) (only printing).
    Eval vm_compute in (interp_list 7 1 [20;30;40]).
    *)
    Lemma interp_list_test_1:
        exists log,
        (interp_list 20 1 [20;30;40]) = (12, (initial 91 nil), log)
    .
    Proof. eexists. reflexivity. Qed.


    Eval vm_compute in (interp_from 10 (ground (initial0
    (
        ((bv_nat 3) + (bv_nat 4)) + ((bv_nat 5) + (bv_nat 6))
    )))).

    Lemma interp_test_2:
        exists rem log,
            (interp_from 10 (ground (initial0
                (
                    ((bv_nat 3) + (bv_nat 4))
                    +
                    ((bv_nat 5) + (bv_nat 6))
                ))))
            = (rem, (ground (initial0 (aoo_operand (bv_nat 18)))), log)
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.


    Lemma interp_test_3:
        exists rem log,
            (interp_from 10 (ground (initial0
                (
                    ((bv_nat 5) * (bv_nat 6))
                    /
                    ((bv_nat 3) + (bv_nat 4))
                    
                ))))
            = (rem, (ground (initial0 (aoo_operand (bv_nat 4)))), log)
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.
End arith.



Module fib_native.

    Import default_builtin.
    Import default_builtin.Notations.

    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).

    Definition X : variable := "X".
    Definition Y : variable := "Y".
    Definition Curr : variable := "Curr".
    Definition Tgt : variable := "Tgt".
    Definition REST_SEQ : variable := "$REST_SEQ".
    
    Definition initialState {_br : BasicResolver} := (apply_symbol "initialState").
    Arguments initialState {_br} _%rs.

    Definition resultState {_br : BasicResolver} := (apply_symbol "resultState").
    Arguments resultState {_br} _%rs.

    Definition state {_br : BasicResolver} := (apply_symbol "state").
    Arguments state {_br} _%rs.

    Definition Decls : list Declaration := [
        decl_rule (
            rule ["just-0"]:
               initialState [ (bov_builtin (bv_Z 0)) ]
            ~> resultState [ (ft_element (aoo_operand (bv_Z 0))) ]
        );
        decl_rule (
            rule ["just-1"]:
               initialState [ (bov_builtin (bv_Z 1)) ]
            ~> resultState [ (ft_element (aoo_operand (bv_Z 1))) ]
        );
        decl_rule (
            rule ["two-or-more"]:
               initialState [ $Tgt ]
            ~> state [
                $Tgt,
                (ft_element (aoo_operand (bv_Z 2))),
                (ft_element (aoo_operand (bv_Z 1))),
                (ft_element (aoo_operand (bv_Z 1))) 
               ]
            where ((~~ ($Tgt ==Z (ft_element (aoo_operand (bv_Z 0)))))
                && (~~ ($Tgt ==Z (ft_element (aoo_operand (bv_Z 1))))))
        );
        decl_rule (
            rule ["step"]:
               state [ $Tgt, $Curr, $X, $Y ]
            ~> state [ $Tgt, ($Curr +Z (ft_element (aoo_operand (bv_Z 1)))), ($X +Z $Y), $X ]
            where (~~ ($Curr ==Z $Tgt))
        );
        decl_rule (
            rule ["result"]:
               state [ $Tgt, $Curr, $X, $Y ]
            ~> resultState [ $X ]
                where (($Curr ==Z $Tgt))
        )
    ].

    Definition Γ : FlattenedRewritingTheory*(list string) := Eval vm_compute in 
    (to_theory (process_declarations (Decls))).


    Definition interp_from (fuel : nat) from
        := interp_in_from Γ fuel from
    .

    Definition initial0 (x : AppliedOperatorOr' symbol builtin_value) :=
        (ground (
            initialState [ x ]
        ))
    .

    Definition fib_interp_from (fuel : nat) (from : Z)
        := interp_in_from Γ fuel (ground (initial0
                (aoo_operand (bv_Z from))))
    .

    Definition fib_interp_from_toint
        (fuel : nat) (from : Z)
    :=
        let r := fib_interp_from fuel from in
        let n : Z := (match r.1.2 with
        | aoo_app (ao_app_operand (ao_operator "resultState") ((bv_Z val)))
          => val
        | _ => Z0
        end) in
        (r.1.1,n,r.2)
    .

    
    Eval vm_compute in (interp_from 50 (ground (initial0
    (
        (aoo_operand (bv_Z 7))
    )))).

    Lemma interp_test_fib_0:
        exists rem log,
            (fib_interp_from 10 0)
            = (rem, (ground (resultState [(aoo_operand (bv_Z 0))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_1:
        exists rem log,
            (fib_interp_from 10 1)
            = (rem, (ground (resultState [(aoo_operand (bv_Z 1))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_2:
        exists rem log,
            (fib_interp_from 10 2)
            = (rem, (ground (resultState [(aoo_operand (bv_Z 1))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_3:
        exists rem log,
            (fib_interp_from 10 3)
            = (rem, (ground (resultState [(aoo_operand (bv_Z 2))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.


    Lemma interp_test_fib_11:
        exists rem log,
            (fib_interp_from 20 11)
            = (rem, (ground (resultState [(aoo_operand (bv_Z 89))])), log)
    .
    Proof. eexists. eexists. Time reflexivity. Qed.



End fib_native.

