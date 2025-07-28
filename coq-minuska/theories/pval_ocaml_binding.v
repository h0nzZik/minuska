From Minuska Require Import spec default_everything.

From Minuska Require Import
    builtin.empty
    builtin.klike
    pi.trivial
    hidden.hidden_unit
.

From Coq Require Import String ZArith.


Record ValueAlgebraInterface (NondetValue : Type) := mkValueAlgebraInterface {
    bi_signature : Signature ;
    bi_beta : Model bi_signature NondetValue ;
    bi_sym_info : string -> SymbolInfo ;
}.

Record HiddenAlgebraInterface (NondetValue : Type)
:= mkHiddenAlgebraInterface {
    hai_vai : ValueAlgebraInterface NondetValue ;
    hai_signature : HiddenSignature ;
    hai_model : HiddenModel _ hai_signature hai_vai.(bi_beta _)  ;
}.

Definition builtins_empty : ValueAlgebraInterface MyUnit := {|
    bi_beta := builtin.empty.β ;
    bi_sym_info := fun s => si_none ;
|}.

Definition builtins_klike : ValueAlgebraInterface MyUnit := {|
    bi_beta := builtin.klike.β ;
    bi_sym_info := builtin.klike.sym_info ;
|}.

Definition pi_trivial := (@pi.trivial.MyProgramInfo string _ MyUnit, @pi.trivial.my_binding).

Definition hai_klike : HiddenAlgebraInterface MyUnit := {|
    hai_vai := builtins_klike ;
    hai_signature := _ ;
    hai_model := unit_hidden_model _ _ _;
|}.

