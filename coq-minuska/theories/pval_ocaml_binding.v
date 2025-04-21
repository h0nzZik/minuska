From Minuska Require Import spec default_everything.

From Minuska Require Import
    builtin.empty
    builtin.klike
    pi.trivial
.

From Coq Require Import String ZArith.

Record BuiltinInterface (NondetValue : Type) := mkBuiltinInterface {
    bi_signature : Signature ;
    bi_beta : Model bi_signature (NondetValue : Type) ;
    bi_bindings : BuiltinsBinding ;
}.

Definition builtins_empty : BuiltinInterface MyUnit := {|
    bi_beta := builtin.empty.β ;
    bi_bindings := builtin.empty.builtins_binding ;
|}.

Definition builtins_klike : BuiltinInterface MyUnit := {|
    bi_beta := builtin.klike.β ;
    bi_bindings := builtin.klike.builtins_binding ;
|}.

Definition pi_trivial := (@pi.trivial.MyProgramInfo, @pi.trivial.my_binding).

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

