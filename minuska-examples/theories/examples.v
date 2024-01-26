From Coq.Logic Require Import ProofIrrelevance.


From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    builtins
    spec_interpreter
    naive_interpreter
    default_static_model
    notations
    frontend
    interp_loop
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

    Definition Γ : RewritingTheory*(list string)
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

    Definition Γ : RewritingTheory*(list string) :=
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

Module two_counters_Z.
#[local]
    Instance Σ : StaticModel := default_model (default_builtin.β).
    Import default_builtin.

    Definition M : variable := "M".
    Definition N : variable := "N".
    
    Definition state {_br : BasicResolver} := (apply_symbol "state").
    Arguments state {_br} _%rs.

    Print Expression.
    Definition Γ : RewritingTheory*(list string) :=
    Eval vm_compute in (to_theory (process_declarations ([
        decl_rule (
            rule ["my-rule"]:
               state [ $M , $N ]
            ~> state [
                (($M) -Z (ft_element (aoo_operand (bv_Z 1)))),
                (($N) +Z ($M))
                ]
            where (($M) >Z (ft_element (aoo_operand (bv_Z 0))))
        )
    ]))).
    

    Definition interp :=
        naive_interpreter Γ.1
    .

    Definition pair_to_state (mn : (Z * Z)%type) : GroundTerm :=
        (ground(
        aoo_app (
            ao_app_operand
                (
                ao_app_operand (ao_operator "state")
                    ((bv_Z mn.1))
                )
                ((bv_Z mn.2))
        )))
    .

    Definition state_to_pair (g : GroundTerm) : option (Z * Z) :=
    match g with
    | aoo_app (
        (ao_app_operand (ao_app_operand (ao_operator "state") ((bv_Z m))) (bv_Z n)))
        => 
            Some (m, n)
    | _ => None
    end
    .

    Definition interp_loop_number fuel := 
        fun (m n : Z) =>
        let fg' := ((interp_loop interp fuel) ∘ pair_to_state) (m,n) in
        state_to_pair fg'.2
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
    
    Definition u_cseq {_br : BasicResolver} := (apply_symbol "cseq").
    Arguments u_cseq {_br} _%rs.

    Definition u_emptyCseq {_br : BasicResolver} := (apply_symbol "emptyCseq").
    Arguments u_emptyCseq {_br} _%rs.

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
                cfg [ u_cseq [ ($X + $Y), $REST_SEQ ] ]
            ~> cfg [ u_cseq [ ($X +Nat $Y) , $REST_SEQ ] ]
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
                cfg [ u_cseq [ ($X - $Y), $REST_SEQ ] ]
            ~> cfg [ u_cseq [ ($X -Nat $Y) , $REST_SEQ ] ]
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
                cfg [ u_cseq [ (($X) * ($Y)), $REST_SEQ ] ]
            ~> cfg [ u_cseq [ ($X *Nat $Y) , $REST_SEQ ] ]
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
                cfg [ u_cseq [ (($X) / ($Y)), $REST_SEQ ] ]
            ~> cfg [ u_cseq [ ($X /Nat $Y) , $REST_SEQ ] ]
                where (
                    (isNat ($X))
                    &&
                    (isNat ($Y))
                )
        );
        decl_strict (symbol "div" of arity 2 strict in [0;1])
    ].

    Definition Γ : RewritingTheory*(list string) := Eval vm_compute in 
    (to_theory (process_declarations (Decls))).


    (*
    Definition initial1 (x y : nat) :=
        (ground (cfg [ u_cseq [ ((@aoo_operand symbol _ (bv_nat x)) + (@aoo_operand symbol _ (bv_nat y))), u_emptyCseq [] ] ]))
    .*)

    Definition initial0 (x : AppliedOperatorOr' symbol builtin_value) :=
        (ground (
            cfg [
                u_cseq [ 
                    x,
                    u_emptyCseq []
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

    Definition Γ : RewritingTheory*(list string) := Eval vm_compute in 
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

    Definition var {_br : BasicResolver} := (apply_symbol "var").
    Arguments var {_br} _%rs.

    (* Utilities *)
    Definition u_cseq_name : string := "u_cseq".
    Definition u_empty_cseq_name : string := "u_empty_cseq".

    Definition u_cseq {_br : BasicResolver} := (apply_symbol u_cseq_name).
    Arguments u_cseq {_br} _%rs.

    Definition u_emptyCseq {_br : BasicResolver} := (apply_symbol u_empty_cseq_name).
    Arguments u_emptyCseq {_br} _%rs.

    Definition u_cfg {_br : BasicResolver} := (apply_symbol "u_cfg").
    Arguments u_cfg {_br} _%rs.

    Definition u_state {_br : BasicResolver} := (apply_symbol "u_state").
    Arguments u_state {_br} _%rs.

    (* Data *)
    Definition unitValue {_br : BasicResolver} := (apply_symbol "unitValue").
    Arguments unitValue {_br} _%rs.


    (* Arithmetics *)
    Definition arith_plus {_br : BasicResolver} := (apply_symbol "arith_plus").
    Arguments arith_plus {_br} _%rs.

    Definition arith_minus {_br : BasicResolver} := (apply_symbol "arith_minus").
    Arguments arith_minus {_br} _%rs.

    Definition arith_times {_br : BasicResolver} := (apply_symbol "arith_times").
    Arguments arith_times {_br} _%rs.

    Definition arith_div {_br : BasicResolver} := (apply_symbol "arith_div").
    Arguments arith_div {_br} _%rs.

    (* Boolean expressions *)

    Definition bexpr_lt {_br : BasicResolver} := (apply_symbol "bexpr_lt").
    Arguments bexpr_lt {_br} _%rs.

    Definition bexpr_le {_br : BasicResolver} := (apply_symbol "bexpr_le").
    Arguments bexpr_le {_br} _%rs.

    Definition bexpr_eq {_br : BasicResolver} := (apply_symbol "bexpr_eq").
    Arguments bexpr_eq {_br} _%rs.

    Definition bexpr_negb {_br : BasicResolver} := (apply_symbol "bexpr_negb").
    Arguments bexpr_negb {_br} _%rs.

    (* Statements *)
    Definition stmt_assign {_br : BasicResolver} := (apply_symbol "stmt_assign").
    Arguments stmt_assign {_br} _%rs.

    Definition stmt_seq {_br : BasicResolver} := (apply_symbol "stmt_seq").
    Arguments stmt_seq {_br} _%rs.

    Definition stmt_ifthenelse {_br : BasicResolver} := (apply_symbol "stmt_ifthenelse").
    Arguments stmt_ifthenelse {_br} _%rs.

    Definition stmt_while {_br : BasicResolver} := (apply_symbol "stmt_while").
    Arguments stmt_while {_br} _%rs.

    Declare Scope LangImpScope.
    Delimit Scope LangImpScope with limp.
    Close Scope LangImpScope.

    Notation "x '+' y" := (arith_plus [ x, y ]) : LangImpScope.
    Notation "x '-' y" := (arith_minus [ x, y ]) : LangImpScope.
    Notation "x '*' y" := (arith_times [ x, y ]) : LangImpScope.
    Notation "x '/' y" := (arith_div [ x, y ]) : LangImpScope.

    Definition builtin_string (s : string) := ((@aoo_operand symbol builtin_value (bv_str s))).

    Notation "x '<=' y" := (bexpr_le [x, y]) (at level 70) : LangImpScope.

    Notation "x '<:=' y" := (stmt_assign [x, y]) (at level 90) : LangImpScope.
    Notation "c ';' 'then' d" := (stmt_seq [c, d]) (at level 90, right associativity) : LangImpScope.
    Notation "'if' c 'then' x 'else' y "
        := (stmt_ifthenelse [c, x, y])
            (at level 200, c at level 200, x at level 200, y at level 200)
            : LangImpScope.


    Notation "'while' c 'do' x 'done'"
    := (stmt_while [c, x])
        : LangImpScope
    .

    Definition isValue :=  fun x =>
         ((isNat x) || (isZ x) || (isBool x) || (isAppliedSymbol "unitValue" x))%rs.

    #[local]
    Instance ImpDefaults : Defaults := {|
        default_cseq_name := u_cseq_name ;
        default_empty_cseq_name := u_empty_cseq_name ;
        default_context_template
            := (context-template u_cfg ([ u_state [HOLE; (aoo_operand ($X)) ] ]) with HOLE) ;

        default_isValue := isValue ;
    |}.


    Notation "'simple_rule' '[' s ']:' l '~>' r 'where' c" := (
        rule [ s ]:
            u_cfg [ u_state [ u_cseq [ l, $REST_SEQ ], $VALUES ] ]
         ~> u_cfg [ u_state [ u_cseq [ r, $REST_SEQ ], $VALUES ] ]
         where c
    ) (at level 90).

    Notation "'simple_rule' '[' s ']:' l '~>' r 'always'" := (
        rule [ s ]:
            u_cfg [ u_state [ u_cseq [ l, $REST_SEQ ], $VALUES ] ]
         ~> u_cfg [ u_state [ u_cseq [ r, $REST_SEQ ], $VALUES ] ]
    ) (at level 90).

    Definition Decls : list Declaration := [
        decl_strict (symbol "arith_plus" of arity 2 strict in [0;1]);
        decl_strict (symbol "arith_minus" of arity 2 strict in [0;1]);
        decl_strict (symbol "arith_times" of arity 2 strict in [0;1]);
        decl_strict (symbol "arith_div" of arity 2 strict in [0;1]);
        (* plus *)
        decl_rule (
            simple_rule ["plus-Z-Z"]:
               ($X + $Y)
            ~> ($X +Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )
        );
        (* minus *)
        decl_rule (
            simple_rule ["minus-Z-Z"]:
               ($X - $Y)
            ~> ($X -Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )
        );
        (* times *)
        decl_rule (
            simple_rule ["times-Z-Z"]:
               (($X) * ($Y))
            ~> ($X *Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )
        );
        (* div *)
        decl_rule (
            simple_rule ["div-Z-Z"]:
                (($X) / ($Y))
            ~> ($X /Z $Y)
                where (
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                    (* TODO test that $Y is not 0*)
                )
        );
        
        decl_strict (symbol "stmt_assign" of arity 2 strict in [1]);
        decl_rule (
            rule ["assign-value"]:
                u_cfg [ u_state [ u_cseq [ (var [$X]) <:= $Y, $REST_SEQ], $VALUES ] ]
            ~> u_cfg [ u_state [
                    u_cseq [unitValue[], $REST_SEQ],
                    (ft_ternary b_map_update ($VALUES) ($X) ($Y))
                ] ]
                where ((isString ($X)) && (isValue ($Y)))
        );
        decl_rule (
            rule ["var-lookup"]:
                u_cfg [ u_state [ u_cseq [ var [$X], $REST_SEQ], $VALUES]]
            ~> u_cfg [ u_state [
                u_cseq [(ft_binary b_map_lookup ($VALUES) ($X)), $REST_SEQ],
                $VALUES
            ]]
        );
        (* TODO stmt_seq does not have to be strict in the second argument, and the following rule does not need to check the value-ness of the second argument*)
        decl_rule (
            simple_rule ["seq-unit-value"]:
                stmt_seq [unitValue [], $X ]
            ~> $X
            where ((isValue ($X)))
        );
        decl_strict (symbol "stmt_seq" of arity 2 strict in [0;1]);

        decl_strict (symbol "bexpr_eq" of arity 2 strict in [0;1]);
        decl_strict (symbol "bexpr_negb" of arity 1 strict in [0]);
        decl_strict (symbol "bexpr_le" of arity 2 strict in [0;1]);
        decl_strict (symbol "bexpr_lt" of arity 2 strict in [0;1]);

        decl_rule (
            simple_rule ["bexpr-eq-Z-Z"]:
                bexpr_eq [ $X, $Y ]
            ~> ((ft_binary b_eq ($X) ($Y)))
            where ((isValue ($X)) && (isValue ($Y)))
        );
        decl_rule (
            simple_rule ["bexpr-le-Z-Z"]:
                bexpr_le [ $X, $Y ]
            ~> ((ft_binary b_Z_isLe ($X) ($Y)))
            where ((isZ ($X)) && (isZ ($Y)))
        );
        decl_rule (
            simple_rule ["bexpr-lt-Z-Z"]:
               bexpr_lt [ $X, $Y ]
            ~> ((ft_binary b_Z_isLt ($X) ($Y)))
            where ((isZ ($X)) && (isZ ($Y)))
        );
        decl_rule (
            simple_rule ["bexpr-negb-bool"]:
               bexpr_negb [$X]
            ~> (ft_unary b_bool_neg ($X))
            where ((isBool ($X)))
        );
        decl_strict (symbol "stmt_ifthenelse" of arity 3 strict in [0]);
        decl_rule (
            simple_rule ["stmt-ite-true"]:
               stmt_ifthenelse [$B, $X, $Y]
            ~> $X
            where ((($B) ==Bool true))
        );
        decl_rule (
            simple_rule ["stmt-ite-false"]:
               stmt_ifthenelse [$B, $X, $Y]
            ~> $Y
            where ((($B) ==Bool false))
        );
        decl_rule (
            simple_rule ["while-unfold"]:
            stmt_while [$B, $X]
            ~> (if ($B) then (($X); then stmt_while [$B, $X]) else (unitValue []))
            always
        )
    ]%limp.

    Definition Γ : RewritingTheory*(list string) := Eval vm_compute in 
    (to_theory (process_declarations (Decls))).

    (* Compute (length (Γ.1)). *)


    Definition initial0 (x : AppliedOperatorOr' symbol builtin_value) :=
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
        unfold RewritingTheory_wf.
        Search forallb.
        rewrite Forall_forall.
        intros r Hr.
        unfold RewritingRule_wf.
        unfold RewritingRule_wf1.
        unfold RewritingRule_wf2.
        split.
        {

        }
    Qed.

    Definition imp_interp_from (fuel : nat) (from : GroundTerm)
        := interp_loop (naive_interpreter Γ.1) fuel (ground (initial0 from))
    .

    (*
    (* Debugging notations *)
    Notation "( x ( y ) )" := (ao_app_ao x y) (only printing).
    Notation "( x ( y ) )" := (ao_app_operand x y) (only printing).
    Notation "( x )" := (ao_operator x) (only printing).
    *)
    (*  
    Compute (imp_interp_from 12 (ground (
        (var [builtin_string "x"]) <:= ((aoo_operand (bv_Z 89))) ; then
        ((aoo_operand (bv_Z 3)) + (var [builtin_string "x"]))
        )%limp)).

    *)

    Lemma test_imp_interp_1:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 12 (ground (
        (var [builtin_string "x"]) <:= ((aoo_operand (bv_Z 89))) ; then
        ((aoo_operand (bv_Z 3)) + (var [builtin_string "x"]))
        )%limp))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(aoo_operand (bv_Z 92)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.
    
    Definition program_2 := (ground (
        (var [builtin_string "x"]) <:= ((aoo_operand (bv_Z 89))) ; then
        (if(
            ( (var [builtin_string "x"]) <= (aoo_operand (bv_Z 90))) )
         then (aoo_operand (bv_Z 10)) else (aoo_operand (bv_Z 20))
        )
        )%limp).

    (* Compute (imp_interp_from 15 program_2). *)
    Lemma test_imp_interp_5:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 15 program_2)
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(aoo_operand (bv_Z 10)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

    Definition program_3 := (ground (
        (var [builtin_string "x"]) <:= ((aoo_operand (bv_Z 91))) ; then
        (if(
            ( (var [builtin_string "x"]) <= (aoo_operand (bv_Z 90))) )
         then (aoo_operand (bv_Z 10)) else (aoo_operand (bv_Z 20))
        )
        )%limp).

    (* Compute (imp_interp_from 15 program_3). *)
    Lemma test_imp_interp_program_3:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 15 program_3)
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(aoo_operand (bv_Z 20)), u_emptyCseq [] ] , m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

    Notation "'v' '(' s ')'" := (var [builtin_string s]).

    (* Definition n {_br : BasicResolver} := (ground(v("n"))). *)

    Definition program_count_to (n : Z) := (ground (
        (v("n")) <:= ((aoo_operand (bv_Z n))) ; then
        (v("sum")) <:= ((aoo_operand (bv_Z 0))) ; then
        (while(((aoo_operand (bv_Z 1)) <= (v("n")))) do (
            (v("sum")) <:= ((v("sum")) + ((v("n")))); then
            (v("n")) <:= ((v("n")) + (aoo_operand (bv_Z (-1))))
        ) done
        );then (v("sum"))
        )%limp).

    Lemma test_imp_interp_program_count_to_3:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 1000 (program_count_to 3))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(aoo_operand (bv_Z 6)), u_emptyCseq [] ] , m ] ]
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
                u_cfg [ u_state [ u_cseq [(aoo_operand (bv_Z 55)), u_emptyCseq [] ] , m ] ]
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
        | aoo_app
          (ao_app_ao (ao_operator "u_cfg")
          (ao_app_operand (
            ao_app_ao 
                (ao_operator "u_state")
                (ao_app_ao
                    ( ao_app_operand
                        (ao_operator "u_cseq")
                        (bv_Z val)
                    )
                    (ao_operator "u_empty_cseq")
                )
        )
           (_) ))
          => val
        | _ => Z0
        end) in
        (r.1,n)
    .

End imp.

