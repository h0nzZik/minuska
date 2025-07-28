From Minuska Require Import spec default_everything.

From Minuska Require Import
    builtin.empty
    builtin.klike
    pi.trivial
    hidden.hidden_unit
.

From Coq Require Import String ZArith.


Variant SymbolInfo (P HP F A M : Type)
    :=
| si_none
| si_predicate (p : P)
| si_hidden_predicate (hp : HP)
| si_function (f : F)
| si_attribute (a : A)
| si_method (m : M)
.


Class ValueAlgebraInterface (NondetValue : Type) := mkValueAlgebraInterface {
    bi_signature :: Signature ;
    bi_beta : Model bi_signature NondetValue ;
}.

Class HiddenAlgebraInterface (NondetValue : Type)
:= mkHiddenAlgebraInterface {
    hai_vai :: ValueAlgebraInterface NondetValue ;
    hai_signature :: HiddenSignature ;
    hai_model : HiddenModel _ hai_signature hai_vai.(bi_beta _)  ;
    bi_sym_info : string -> SymbolInfo builtin_predicate_symbol HiddenPredicateSymbol builtin_function_symbol AttributeSymbol MethodSymbol ;
}.

Definition builtins_empty : ValueAlgebraInterface MyUnit := {|
    bi_beta := builtin.empty.β ;
|}.

Definition builtins_klike : ValueAlgebraInterface MyUnit := {|
    bi_beta := builtin.klike.β ;
|}.

Definition pi_trivial := (@pi.trivial.MyProgramInfo string _ MyUnit, @pi.trivial.my_binding).

Definition klike_sym_info : string -> SymbolInfo klike.PredicateSymbol void _ void void:=
fun s => match s with
| "sym.is" => si_predicate _ _ _ _ _ (klike.b_isSymbol)
| "sym.isNot" => si_predicate _ _ _ _ _ builtin.klike.b_isNotSymbol
| "bool.is" => si_predicate _ _ _ _ _ b_isBool
| "bool.isNot" => si_predicate _ _ _ _ _ b_isNotBool
| "string.is" => si_predicate _ _ _ _ _ b_isString
| "string.isNot" => si_predicate _ _ _ _ _ b_isNotString
| "z.is" => si_predicate _ _ _ _ _ b_isZ
| "z.isNot" => si_predicate _ _ _ _ _ b_isNotZ
| "bool.neg" => si_function _ _ _ _ _ b_bool_neg
| "bool.is_true" => si_predicate _ _ _ _ _ b_bool_is_true
| "bool.is_false" => si_predicate _ _ _ _ _ b_bool_is_false
| "term.eq" => si_predicate _ _ _ _ _ b_term_eq
| "term.same_symbol" =>  si_predicate _ _ _ _ _ b_have_same_symbol
| "term.different_symbol" => si_predicate _ _ _ _ _ b_have_different_symbols
| "z.plus" => si_function _ _ _ _ _ b_Z_plus
| "z.minus" => si_function _ _ _ _ _ b_Z_minus
| "z.eq" => si_function _ _ _ _ _ b_Z_eq
| "z.le" => si_function _ _ _ _ _ b_Z_isLe
| "z.lt" => si_function _ _ _ _ _ b_Z_isLt
| "map.hasKey" => si_predicate _ _ _ _ _ b_map_hasKey
| "map.lookup" => si_function _ _ _ _ _ b_map_lookup
| "map.size" => si_function _ _ _ _ _ b_map_size
| "map.empty" => si_function _ _ _ _ _ b_map_empty
| "map.update" => si_function _ _ _ _ _ b_map_update
| _ => si_none _ _ _ _ _
end.

Definition hai_klike : HiddenAlgebraInterface MyUnit := {|
    hai_vai := builtins_klike ;
    hai_signature := (unit_hidden_signature _) ;
    hai_model := unit_hidden_model _ _ _;
    bi_sym_info := klike_sym_info ;
|}.

