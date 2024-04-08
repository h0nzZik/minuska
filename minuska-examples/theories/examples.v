From Coq.Logic Require Import ProofIrrelevance.


From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    builtins
    spec_interpreter
    naive_interpreter
    interpreter_results
    default_static_model
    notations
    frontend
    interp_loop
    example
.

Variant Act := default_act | invisible_act.

#[global]
Instance Act_eqDec : EqDecision Act.
Proof.
    ltac1:(solve_decision).
Defined.

(* moved to main library*)
(*
Module example_1.

    #[local]
    Instance Σ : StaticModel :=
        default_model (default_builtin.β)
    .
    
    Definition X : variable := "X".

    Definition cfg {_br : BasicResolver} := (@t_term _ operand_type "cfg").
    Arguments cfg {_br} _%_rs.

    Definition s {_br : BasicResolver} := (@t_term _ operand_type "s").
    Arguments s {_br} _%_rs.

    Definition Decls : list Declaration := [
        decl_rule (
            rule ["my_rule"]:
                cfg [ s [ s [ (inject_variable X) ] ] ]
                ~>{default_act} cfg [ $X ]
        )
    ].

    About process_declarations.
    Definition Γ : (RewritingTheory2 Act)*(list string)
        := Eval vm_compute in (to_theory Act (process_declarations Act default_act (Decls))).

    Definition interp :=
        naive_interpreter Γ.1
    .

    (* TODO remove *)
    Fixpoint interp_loop
        (fuel : nat)
        (g : (TermOver builtin_value))
        : (nat*(TermOver builtin_value))
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

    Fixpoint my_number' (n : nat) : PreTerm' symbol builtin_value  :=
    match n with
    | 0 => pt_operator "0"
    | S n' => pt_app_ao (pt_operator "s") (my_number' n')
    end
    .

    Fixpoint my_number'_inv
        (g : PreTerm' symbol builtin_value)
        : option nat
    :=
    match g with
    | pt_operator s => if bool_decide (s = "0") then Some 0 else None
    | pt_app_ao s arg =>
        match s with
        | pt_operator s => if bool_decide (s = "s") then
            n ← my_number'_inv arg;
            Some (S n)
        else None
        | _ => None
        end
    | pt_app_operand _ _ => None
    end
    .

    Definition my_number (n : nat) : (TermOver builtin_value) :=
        term_preterm (pt_app_ao (pt_operator "cfg") (my_number' n))
    .

    Definition my_number_inv (g : (TermOver builtin_value)) : option nat
    :=
    match g with
    | term_preterm (pt_app_ao (pt_operator "cfg") g') => my_number'_inv g'
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
*)


Module two_counters.

    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).


    Definition M : variable := "M".
    Definition N : variable := "N".
    
    Definition cfg {_br : BasicResolver} := (@t_term _ operand_type "cfg").
    Arguments cfg {_br} _%_rs.

    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Definition s {_br : BasicResolver} := (@t_term _ operand_type "s").
    Arguments s {_br} _%_rs.

    Definition Γ : (RewritingTheory2 Act)*(list string) :=
    Eval vm_compute in (to_theory Act (process_declarations Act default_act ([
        decl_rule (
            rule ["my-rule"]:
                cfg [ state [ s [ t_over ($M) ], t_over ($N) ] ]
            ~>{default_act} cfg [ state [ t_over ($M), s [ t_over ($N) ]  ] ]
        )
    ]))).
    

    Definition interp :=
        naive_interpreter Γ.1
    .

    Definition pair_to_state (mn : nat*nat) : (TermOver builtin_value) :=
        t_term "cfg" [(t_term "state" [(example.example_1.my_number' mn.1);(example.example_1.my_number' mn.2)])]
    .

    Definition state_to_pair (g : (TermOver builtin_value)) : option (nat*nat) :=
    match g with
    | t_term "cfg" [(t_term "state" [(m');(n')])] =>
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

Module two_counters_Z.
#[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).
    Import default_builtin.

    Definition M : variable := "M".
    Definition N : variable := "N".
    
    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Coercion Z_to_builtin (x : Z) := (e_ground (t_over (bv_Z x))).

    Definition Γ : (RewritingTheory2 Act)*(list string) :=
    Eval vm_compute in (to_theory Act (process_declarations Act default_act ([
        decl_rule (
            rule ["my-rule"]:
               state [ t_over ($M) ; t_over ($N) ]
            ~>{default_act} state [
                t_over ((($M)) -Z 1%Z);
                t_over (($N) +Z (($M)))
                ]
            where ($M >Z 0%Z)
        )
    ]))).
    

    Definition interp :=
        naive_interpreter Γ.1
    .

    Definition pair_to_state (mn : (Z * Z)%type) : (TermOver builtin_value) :=
        (ground(
            t_term "state" [t_over (bv_Z mn.1); t_over (bv_Z mn.2)]
        ))
    .

    Definition state_to_pair (g : (TermOver builtin_value)) : option (Z * Z) :=
    match g with
    | t_term "state" [t_over (bv_Z m); t_over (bv_Z n)] =>
            Some (m, n)
    | _ => None
    end
    .

    Definition interp_loop_number (fuel : nat) := 
        fun (m n : Z) =>
        let fg' := (((interp_in_from Γ fuel)) ∘ pair_to_state) (m,n) in
        state_to_pair fg'.1.2
    .

End two_counters_Z.

Module arith.

    Import default_builtin.
    Import default_builtin.Notations.

    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).

    Definition X : variable := "X".
    Definition Y : variable := "Y".
    Definition REST_SEQ : variable := "$REST_SEQ".
    
    Definition u_cseq {_br : BasicResolver} := (@t_term _ operand_type "cseq").
    Arguments u_cseq {_br} _%_rs.

    Definition u_emptyCseq {_br : BasicResolver} := (@t_term _ operand_type "emptyCseq").
    Arguments u_emptyCseq {_br} _%_rs.

    Definition plus {_br : BasicResolver} := (@t_term _ operand_type "plus").
    Arguments plus {_br} _%_rs.

    Definition minus {_br : BasicResolver} := (@t_term _ operand_type "minus").
    Arguments minus {_br} _%_rs.

    Definition times {_br : BasicResolver} := (@t_term _ operand_type "times").
    Arguments times {_br} _%_rs.

    Definition div {_br : BasicResolver} := (@t_term _ operand_type "div").
    Arguments div {_br} _%_rs.

    Definition cfg {_br : BasicResolver} := (@t_term _ operand_type "cfg").
    Arguments cfg {_br} _%_rs.

    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Definition s {_br : BasicResolver} := (@t_term _ operand_type "s").
    Arguments s {_br} _%_rs.

    Definition freezer {_br : BasicResolver} (sym : symbol) (position : nat)
    :=
        (@t_term _ operand_type ("freezer_" +:+ sym +:+ "_" +:+ (pretty position)))
    .
    Arguments freezer {_br} _%_rs.


    Declare Scope LangArithScope.
    Delimit Scope LangArithScope with larith.

    Notation "x '+' y" := (plus [ x, y ])%larith.
    Notation "x '-' y" := (minus [ x, y ])%larith.
    Notation "x '*' y" := (times [ x, y ])%larith.
    Notation "x '/' y" := (div [ x, y ])%larith.

    Open Scope larith.

    #[local]
    Instance ArithDefaults : Defaults := {|
        default_cseq_name := "cseq" ;
        default_empty_cseq_name := "emptyCseq" ;
        default_context_template
            := (context-template cfg [ HOLE ] with HOLE) ;

        default_isValue := fun x => (isNat x) ;
    |}.

    Definition Decls : list Declaration := [
        (* plus *)
        decl_rule (
            rule ["plus-nat-nat"]:
                cfg [ u_cseq [ (t_over ($X) + t_over ($Y) ), t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X +Nat $Y) , t_over ($REST_SEQ) ] ]
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
                cfg [ u_cseq [ (t_over ($X) - t_over ($Y)), t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X -Nat $Y) , t_over ($REST_SEQ) ] ]
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
                cfg [ u_cseq [ (t_over ($X) * t_over ($Y)), t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X *Nat $Y) , t_over ($REST_SEQ) ] ]
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
                cfg [ u_cseq [ (t_over ($X) / t_over ($Y)), t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X /Nat $Y) , t_over ($REST_SEQ) ] ]
                where (
                    (isNat ($X))
                    &&
                    (isNat ($Y))
                )
        );
        decl_strict (symbol "div" of arity 2 strict in [0;1])
    ].

    Definition Γ : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act (Decls))).


    (*
    Definition initial1 (x y : nat) :=
        (ground (cfg [ u_cseq [ ((@term_operand symbol _ (bv_nat x)) + (@term_operand symbol _ (bv_nat y))), u_emptyCseq [] ] ]))
    .*)

    Definition initial0 (x : TermOver builtin_value) :=
        (ground (
            cfg [
                u_cseq [ 
                    x;
                    u_emptyCseq []
                    ]
                ]
            )
        )
    .

    Definition initial (x: nat) (ly : list nat) :=
        (ground (initial0 ((foldr 
            (fun a (b : TermOver builtin_value) =>
                plus [(t_over (bv_nat a)) , b]
            )
            (t_over (bv_nat x))
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
    Notation "( x ( y ) )" := (pt_app_ao x y) (only printing).
    Notation "( x ( y ) )" := (pt_app_operand x y) (only printing).
    Notation "( x )" := (pt_operator x) (only printing).
    Eval vm_compute in (interp_list 7 1 [20;30;40]).
    *)
    Lemma interp_list_test_1:
        exists log,
        (interp_list 20 1 [20;30;40]) = (12, (initial 91 nil), log)
    .
    Proof. eexists. reflexivity. Qed.


    Eval vm_compute in (interp_from 10 (ground (initial0
    (
        (t_over (bv_nat 3) + t_over (bv_nat 4)) + (t_over (bv_nat 5) + t_over (bv_nat 6))
    )))).

    Lemma interp_test_2:
        exists rem log,
            (interp_from 10 (ground (initial0
                (
                    (t_over (bv_nat 3) + t_over (bv_nat 4))
                    +
                    (t_over (bv_nat 5) + t_over (bv_nat 6))
                ))))
            = (rem, (ground (initial0 ((t_over  (bv_nat 18))))), log)
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.


    Lemma interp_test_3:
        exists rem log,
            (interp_from 10 (ground (initial0
                (
                    (t_over (bv_nat 5) * t_over (bv_nat 6))
                    /
                    (t_over (bv_nat 3) + t_over (bv_nat 4))
                    
                ))))
            = (rem, (ground (initial0 (t_over (bv_nat 4)))), log)
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
    
    Definition initialState {_br : BasicResolver} := (@t_term _ operand_type "initialState").
    Arguments initialState {_br} _%_rs.

    Definition resultState {_br : BasicResolver} := (@t_term _ operand_type "resultState").
    Arguments resultState {_br} _%_rs.

    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Definition Decls : list Declaration := [
        decl_rule (
            rule ["just-0"]:
               initialState [ t_over  (bov_builtin (bv_Z 0)) ]
            ~>{default_act} resultState [ t_over  (e_ground (t_over (bv_Z 0))) ]
        );
        decl_rule (
            rule ["just-1"]:
               initialState [ t_over (bov_builtin (bv_Z 1)) ]
            ~>{default_act} resultState [ t_over  (e_ground (t_over  (bv_Z 1))) ]
        );
        decl_rule (
            rule ["two-or-more"]:
               initialState [ t_over  ($Tgt) ]
            ~>{default_act} state [
                t_over ($Tgt),
                t_over (e_ground (t_over  (bv_Z 2))),
                t_over (e_ground (t_over  (bv_Z 1))),
                t_over (e_ground (t_over  (bv_Z 1))) 
               ]
            where ((~~ ($Tgt ==Z (e_ground (t_over (bv_Z 0)))))
                && (~~ ($Tgt ==Z (e_ground (t_over (bv_Z 1))))))
        );
        decl_rule (
            rule ["step"]:
               state [ t_over ($Tgt); t_over  ($Curr); t_over ($X); t_over ($Y) ]
            ~>{default_act} state [ t_over ($Tgt); t_over (($Curr) +Z (e_ground (t_over  (bv_Z 1)))); t_over ($X +Z $Y); t_over ($X) ]
            where (~~ ($Curr ==Z $Tgt))
        );
        decl_rule (
            rule ["result"]:
               state [ t_over ($Tgt); t_over ($Curr); t_over ($X); t_over ($Y) ]
            ~>{default_act} resultState [ t_over ($X) ]
                where (($Curr ==Z $Tgt))
        )
    ].

    Definition Γ : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act (Decls))).


    Definition interp_from (fuel : nat) from
        := interp_in_from Γ fuel from
    .

    Definition initial0 (x : TermOver builtin_value) :=
        (ground (
            initialState [ x ]
        ))
    .

    Definition fib_interp_from (fuel : nat) (from : Z)
        := interp_in_from Γ fuel (ground (initial0
                (t_over (bv_Z from))))
    .

    Definition fib_interp_from_toint
        (fuel : nat) (from : Z)
    :=
        let r := fib_interp_from fuel from in
        let n : Z := (match r.1.2 with
          t_term "resultState" [t_over (bv_Z val)]
          => val
        | _ => Z0
        end) in
        (r.1.1,n,r.2)
    .

    
    Eval vm_compute in (interp_from 50 (ground (initial0
    (
        (t_over (bv_Z 7))
    )))).

    Lemma interp_test_fib_0:
        exists rem log,
            (fib_interp_from 10 0)
            = (rem, (ground (resultState [(t_over (bv_Z 0))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_1:
        exists rem log,
            (fib_interp_from 10 1)
            = (rem, (ground (resultState [(t_over  (bv_Z 1))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_2:
        exists rem log,
            (fib_interp_from 10 2)
            = (rem, (ground (resultState [(t_over  (bv_Z 1))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_3:
        exists rem log,
            (fib_interp_from 10 3)
            = (rem, (ground (resultState [(t_over  (bv_Z 2))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.


    Lemma interp_test_fib_11:
        exists rem log,
            (fib_interp_from 20 11)
            = (rem, (ground (resultState [(t_over (bv_Z 89))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.



End fib_native.


Module imp.

    Import default_builtin.
    Import default_builtin.Notations.

    #[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).


    Definition B : variable := "$B".
    Definition X : variable := "$X".
    Definition Y : variable := "$Y".
    Definition VALUES : variable := "$VALUES".
    Definition REST_SEQ : variable := "$REST_SEQ".

    Definition var {_br : BasicResolver} := (@t_term _ operand_type "var").
    Arguments var {_br} _%_rs.

    (* Utilities *)
    Definition u_cseq_name : string := "u_cseq".
    Definition u_empty_cseq_name : string := "u_empty_cseq".

    Definition u_cseq {_br : BasicResolver} := (@t_term _ operand_type u_cseq_name).
    Arguments u_cseq {_br} _%_rs.

    Definition u_emptyCseq {_br : BasicResolver} := (@t_term _ operand_type u_empty_cseq_name).
    Arguments u_emptyCseq {_br} _%_rs.

    Definition u_cfg {_br : BasicResolver} := (@t_term _ operand_type "u_cfg").
    Arguments u_cfg {_br} _%_rs.

    Definition u_state {_br : BasicResolver} := (@t_term _ operand_type "u_state").
    Arguments u_state {_br} _%_rs.

    (* Data *)
    Definition unitValue {_br : BasicResolver} := (@t_term _ operand_type "unitValue").
    Arguments unitValue {_br} _%_rs.


    (* Arithmetics *)
    Definition arith_plus {_br : BasicResolver} := (@t_term _ operand_type "arith_plus").
    Arguments arith_plus {_br} _%_rs.

    Definition arith_minus {_br : BasicResolver} := (@t_term _ operand_type "arith_minus").
    Arguments arith_minus {_br} _%_rs.

    Definition arith_times {_br : BasicResolver} := (@t_term _ operand_type "arith_times").
    Arguments arith_times {_br} _%_rs.

    Definition arith_div {_br : BasicResolver} := (@t_term _ operand_type "arith_div").
    Arguments arith_div {_br} _%_rs.

    (* Boolean expressions *)

    Definition bexpr_lt {_br : BasicResolver} := (@t_term _ operand_type "bexpr_lt").
    Arguments bexpr_lt {_br} _%_rs.

    Definition bexpr_le {_br : BasicResolver} := (@t_term _ operand_type "bexpr_le").
    Arguments bexpr_le {_br} _%_rs.

    Definition bexpr_eq {_br : BasicResolver} := (@t_term _ operand_type "bexpr_eq").
    Arguments bexpr_eq {_br} _%_rs.

    Definition bexpr_negb {_br : BasicResolver} := (@t_term _ operand_type "bexpr_negb").
    Arguments bexpr_negb {_br} _%_rs.

    (* Statements *)
    Definition stmt_assign {_br : BasicResolver} := (@t_term _ operand_type "stmt_assign").
    Arguments stmt_assign {_br} _%_rs.

    Definition stmt_seq {_br : BasicResolver} := (@t_term _ operand_type "stmt_seq").
    Arguments stmt_seq {_br} _%_rs.

    Definition stmt_ite {_br : BasicResolver} := (@t_term _ operand_type "stmt_ite").
    Arguments stmt_ite {_br} _%_rs.

    Definition stmt_while {_br : BasicResolver} := (@t_term _ operand_type "stmt_while").
    Arguments stmt_while {_br} _%_rs.

    Declare Scope LangImpScope.
    Delimit Scope LangImpScope with limp.
    Close Scope LangImpScope.

    Notation "x '+' y" := (arith_plus [ x, y ]) : LangImpScope.
    Notation "x '-' y" := (arith_minus [ x, y ]) : LangImpScope.
    Notation "x '*' y" := (arith_times [ x, y ]) : LangImpScope.
    Notation "x '/' y" := (arith_div [ x, y ]) : LangImpScope.

    Definition builtin_string (s : string) := ((@term_operand symbol builtin_value (bv_str s))).

    Notation "x '<=' y" := (bexpr_le [x, y]) (at level 70) : LangImpScope.

    Notation "x '<:=' y" := (stmt_assign [x, y]) (at level 90) : LangImpScope.
    Notation "c ';' 'then' d" := (stmt_seq [c, d]) (at level 90, right associativity) : LangImpScope.
    Notation "'if' c 'then' x 'else' y "
        := (stmt_ite [c, x, y])
            (at level 200, c at level 200, x at level 200, y at level 200)
            : LangImpScope.


    Notation "'while' c 'do' x 'done'"
    := (stmt_while [c, x])
        : LangImpScope
    .

    Definition isValue (x : Expression2) : Expression2 :=
         ((isNat x) || (isZ x) || (isBool x) || (isAppliedSymbol "unitValue" x))%rs
    .

    #[local]
    Instance ImpDefaults : Defaults := {|
        default_cseq_name := u_cseq_name ;
        default_empty_cseq_name := u_empty_cseq_name ;
        default_context_template
            := (context-template u_cfg ([ u_state [HOLE; (term_operand ($X)) ] ]) with HOLE) ;

        default_isValue := isValue ;
    |}.


    Notation "'decl_simple_rule' '[' s ']:' l '~>' r 'where' c" := (
        decl_rule (
        rule [ s ]:
            u_cfg [ u_state [ u_cseq [ l, $REST_SEQ ], $VALUES ] ]
         ~>{default_act} u_cfg [ u_state [ u_cseq [ r, $REST_SEQ ], $VALUES ] ]
         where (c)
        )
    ) (at level 90).

    Notation "'decl_simple_rule' '[' s ']:' l '~>' r 'always'" := (
        decl_rule (
        rule [ s ]:
            u_cfg [ u_state [ u_cseq [ l, $REST_SEQ ], $VALUES ] ]
         ~>{default_act} u_cfg [ u_state [ u_cseq [ r, $REST_SEQ ], $VALUES ] ]
        )
    ) (at level 90).

    Definition Decls : list Declaration := [
        decl_strict (symbol "arith_plus" of arity 2 strict in [0;1]);
        decl_strict (symbol "arith_minus" of arity 2 strict in [0;1]);
        decl_strict (symbol "arith_times" of arity 2 strict in [0;1]);
        decl_strict (symbol "arith_div" of arity 2 strict in [0;1]);
        (* plus *)
        decl_simple_rule ["plus-Z-Z"]: ($X + $Y) ~> ($X +Z $Y) where ((isZ ($X)) && (isZ ($Y)));
        (* minus *)
        decl_simple_rule ["minus-Z-Z"]:
               ($X - $Y)
            ~> ($X -Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )
        ;
        (* times *)
        decl_simple_rule ["times-Z-Z"]:
               (($X) * ($Y))
            ~> ($X *Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )
        ;
        (* div *)
        decl_simple_rule ["div-Z-Z"]:
                (($X) / ($Y))
            ~> ($X /Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                    (* TODO test that $Y is not 0*)
                )
        ;
        
        decl_strict (symbol "stmt_assign" of arity 2 strict in [1]);

        decl_rule (
            rule ["assign-value"]:
                u_cfg [ u_state [ u_cseq [ (var [$X]) <:= $Y, $REST_SEQ], $VALUES ] ]
            ~>{default_act} u_cfg [ u_state [
                    u_cseq [unitValue[], $REST_SEQ],
                    (ft_ternary b_map_update ($VALUES) ($X) ($Y))
                ] ]
                where ((isString ($X)) && (isValue ($Y)))
        );
        decl_rule (
            rule ["var-lookup"]:
                u_cfg [ u_state [ u_cseq [ var [$X], $REST_SEQ], $VALUES]]
            ~>{default_act} u_cfg [ u_state [
                u_cseq [(ft_binary b_map_lookup ($VALUES) ($X)), $REST_SEQ],
                $VALUES
            ]]
        );
        (* TODO stmt_seq does not have to be strict in the second argument, and the following rule does not need to check the value-ness of the second argument*)
        decl_simple_rule ["seq-unit-value"]:
                stmt_seq [unitValue [], $X ]
            ~> $X
            where ((isValue ($X)))
        ;
        decl_strict (symbol "stmt_seq" of arity 2 strict in [0;1]);

        decl_strict (symbol "bexpr_eq" of arity 2 strict in [0;1]);
        decl_strict (symbol "bexpr_negb" of arity 1 strict in [0]);
        decl_strict (symbol "bexpr_le" of arity 2 strict in [0;1]);
        decl_strict (symbol "bexpr_lt" of arity 2 strict in [0;1]);

        decl_simple_rule ["bexpr-eq-Z-Z"]:
                bexpr_eq [ $X, $Y ]
            ~> ((ft_binary b_eq ($X) ($Y)))
            where ((isValue ($X)) && (isValue ($Y)))
        ;
        decl_simple_rule ["bexpr-le-Z-Z"]:
                bexpr_le [ $X, $Y ]
            ~> ((ft_binary b_Z_isLe ($X) ($Y)))
            where ((isZ ($X)) && (isZ ($Y)))
        ;
        decl_simple_rule ["bexpr-lt-Z-Z"]:
               bexpr_lt [ $X, $Y ]
            ~> ((ft_binary b_Z_isLt ($X) ($Y)))
            where ((isZ ($X)) && (isZ ($Y)))
        ;
        decl_simple_rule ["bexpr-negb-bool"]:
               bexpr_negb [$X]
            ~> (ft_unary b_bool_neg ($X))
            where ((isBool ($X)))
        ;
        decl_strict (symbol "stmt_ite" of arity 3 strict in [0]) ;
        decl_simple_rule ["stmt-ite-true"]: stmt_ite [$B, $X, $Y] ~> $X where ($B) ;
        decl_simple_rule ["stmt-ite-false"]: stmt_ite [$B, $X, $Y] ~> $Y where ($B ==Bool false) ;
        (* (* sugared *)
        decl_simple_rule ["while-unfold"]:
            stmt_while [$B, $X]
            ~> (if ($B) then (($X); then stmt_while [$B, $X]) else (unitValue []))
            always
        *)
        decl_simple_rule ["while-unfold"]:
            stmt_while [$B, $X]
            ~> stmt_ite [$B, stmt_seq [$X, stmt_while [$B, $X]], unitValue [] ]
            where (true)
    ]%limp.

    Definition Γ : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act (Decls))).

    (* Compute (length (Γ.1)). *)


    Definition initial0 (x : Term' symbol builtin_value) :=
        (ground (
            u_cfg [ u_state [ u_cseq [x, u_emptyCseq [] ] , (builtin_nullary_function_interp b_map_empty) ] ]
        ))
    .

    Lemma interp_sound:
        FlatInterpreter_sound'
        (Γ.1)
        (naive_interpreter Γ.1) 
    .
    Proof.
        apply naive_interpreter_sound.
        ltac1:(assert(Htmp: isSome(RewritingTheory_wf_heuristics (Γ.1)))).
        {
            ltac1:(compute_done).
        }
        unfold is_true, isSome in Htmp.
        destruct (RewritingTheory_wf_heuristics Γ.1) eqn:Heq>[|inversion Htmp].
        assumption.
    Qed.

    Definition imp_interp_from (fuel : nat) (from : (TermOver builtin_value))
        := interp_loop (naive_interpreter Γ.1) fuel (ground (initial0 from))
    .

    (*
    (* Debugging notations *)
    Notation "( x ( y ) )" := (pt_app_ao x y) (only printing).
    Notation "( x ( y ) )" := (pt_app_operand x y) (only printing).
    Notation "( x )" := (pt_operator x) (only printing).
    *)
    (*  
    Compute (imp_interp_from 12 (ground (
        (var [builtin_string "x"]) <:= ((term_operand (bv_Z 89))) ; then
        ((term_operand (bv_Z 3)) + (var [builtin_string "x"]))
        )%limp)).

    *)

    Lemma test_imp_interp_1:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 12 (ground (
        (var [builtin_string "x"]) <:= ((term_operand (bv_Z 89))) ; then
        ((term_operand (bv_Z 3)) + (var [builtin_string "x"]))
        )%limp))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(term_operand (bv_Z 92)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.
    
    Definition program_2 := (ground (
        (var [builtin_string "x"]) <:= ((term_operand (bv_Z 89))) ; then
        (if(
            ( (var [builtin_string "x"]) <= (term_operand (bv_Z 90))) )
         then (term_operand (bv_Z 10)) else (term_operand (bv_Z 20))
        )
        )%limp).

    (* Compute (imp_interp_from 15 program_2). *)
    Lemma test_imp_interp_5:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 15 program_2)
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(term_operand (bv_Z 10)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

    Definition program_3 := (ground (
        (var [builtin_string "x"]) <:= ((term_operand (bv_Z 91))) ; then
        (if(
            ( (var [builtin_string "x"]) <= (term_operand (bv_Z 90))) )
         then (term_operand (bv_Z 10)) else (term_operand (bv_Z 20))
        )
        )%limp).

    (* Compute (imp_interp_from 15 program_3). *)
    Lemma test_imp_interp_program_3:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 15 program_3)
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(term_operand (bv_Z 20)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

    Notation "'v' '(' s ')'" := (var [builtin_string s]).

    (* Definition n {_br : BasicResolver} := (ground(v("n"))). *)

    Definition program_count_to (n : Z) := (ground (
        (v("n")) <:= ((term_operand (bv_Z n))) ; then
        (v("sum")) <:= ((term_operand (bv_Z 0))) ; then
        (while(((term_operand (bv_Z 1)) <= (v("n")))) do (
            (v("sum")) <:= ((v("sum")) + ((v("n")))); then
            (v("n")) <:= ((v("n")) + (term_operand (bv_Z (-1))))
        ) done
        );then (v("sum"))
        )%limp).

    Lemma test_imp_interp_program_count_to_3:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 1000 (program_count_to 3))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(term_operand (bv_Z 6)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

    (* The proof and QED time of this lemma are too high, so I do not want to run them every time I compile this file.*)
    (*
    Lemma test_imp_interp_program_count_to_10:
        exists (rem : nat) (log : string) (m : BuiltinValue),
        (imp_interp_from 1000 (program_count_to 10))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(term_operand (bv_Z 55)), u_emptyCseq [] ] , m ] ]
            )%limp),
            log
        )
    .
    Proof.
        eexists. eexists. eexists. reflexivity.
    Qed.
    *)

    


    Definition interp_program_count_to (fuel : nat) (n : Z)
    :=
        let r := imp_interp_from fuel (program_count_to n) in
        let n : Z := (match r.2 with
        | term_preterm
          (pt_app_ao (pt_operator "u_cfg")
          (pt_app_operand (
            pt_app_ao 
                (pt_operator "u_state")
                (pt_app_ao
                    ( pt_app_operand
                        (pt_operator "u_cseq")
                        (bv_Z val)
                    )
                    (pt_operator "u_empty_cseq")
                )
        )
           (_) ))
          => val
        | _ => Z0
        end) in
        (r.1,n)
    .

End imp.

