From Minuska Require Import spec default_everything.

From Minuska Require Import
    builtin.empty
    builtin.klike
    pi.trivial
.

From Coq Require Import String ZArith.

Record BuiltinInterface (NondetValue : Type) := {
    bi_beta : Builtin (NondetValue : Type) ;
    bi_bindings : BuiltinsBinding ;
    bi_inject_bool : forall (Fret : option (@builtin_value _ _ NondetValue bi_beta) -> (@builtin_value _ _ NondetValue bi_beta)), bool -> (@builtin_value _ _ NondetValue bi_beta) ;
    bi_inject_Z : forall (Fret : option (@builtin_value _ _ NondetValue bi_beta) -> (@builtin_value _ _ NondetValue bi_beta)), Z -> (@builtin_value _ _ NondetValue bi_beta) ;
    bi_inject_string : forall (Fret : option (@builtin_value _ _ NondetValue bi_beta) -> (@builtin_value _ _ NondetValue bi_beta)), string -> (@builtin_value _ _ NondetValue bi_beta) ;
    bi_eject : (@builtin_value _ _ NondetValue bi_beta) -> option (bool+(Z+(string+unit)))%type ;
}.

Definition builtins_empty : BuiltinInterface MyUnit := {|
    bi_beta := builtin.empty.β ;
    bi_bindings := builtin.empty.builtins_binding ;
    bi_inject_bool := @builtin.empty.inject_bool string;
    bi_inject_Z := @builtin.empty.inject_Z string;
    bi_inject_string := @builtin.empty.inject_string string;
    bi_eject := @builtin.empty.eject string;
|}.

Definition builtins_klike : BuiltinInterface MyUnit := {|
    bi_beta := builtin.klike.β ;
    bi_bindings := builtin.klike.builtins_binding ;
    bi_inject_bool := fun b => @builtin.klike.inject_bool string b;
    bi_inject_Z := fun z => @builtin.klike.inject_Z string z;
    bi_inject_string := fun s => @builtin.klike.inject_string string s;
    bi_eject := @builtin.klike.eject string;
|}.
(* 
Record PI_interface := {
    pii_program_info : 
        forall
        {symbol : Type}
        {symbols : Symbols symbol}
        {NondetValue : Type}
        {builtin : Builtin NondetValue},
        @ProgramInfo symbol symbols NondetValue builtin
        ;
    
    pii_binding : list (string*string) ;
}.

Definition pi_trivial : PI_interface := {
    pii_program_info : trivial.MyProgramInfo ;
}. *)

