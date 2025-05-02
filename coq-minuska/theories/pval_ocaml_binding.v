From Minuska Require Import spec default_everything.

From Minuska Require Import
    builtin.empty
    builtin.klike
    pi.trivial
.

From Coq Require Import String ZArith.


Record BuiltinInterface (NondetValue : Type) := mkBuiltinInterface {
    bi_signature : Signature ;
    bi_beta : Model bi_signature NondetValue ;
    bi_sym_info : string -> SymbolInfo ;
}.

Definition builtins_empty : BuiltinInterface MyUnit := {|
    bi_beta := builtin.empty.β ;
    bi_sym_info := fun s => si_none ;
|}.

Definition builtins_klike : BuiltinInterface MyUnit := {|
    bi_beta := builtin.klike.β ;
    bi_sym_info := builtin.klike.sym_info ;
|}.

Definition pi_trivial := (@pi.trivial.MyProgramInfo string _ MyUnit, @pi.trivial.my_binding).


