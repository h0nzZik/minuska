From Minuska Require Import
    prelude
    spec
    ocaml_interface
.

Definition unit_hidden_signature
    (signature : Signature)
:
    HiddenSignature
:= {|
    AttrSymbol := void ;
    MethSymbol := void ;
    HPredSymbol := void ;
|}.


Definition unit_hidden_model
    {TermSymbol : Type}
    {TermSymbols : Symbols TermSymbol}
    (signature : Signature)
    (NondetValue : Type)
    (model : Model signature NondetValue)
:
    @HiddenModel TermSymbol TermSymbols signature (unit_hidden_signature signature) NondetValue model
:= {|
    HiddenValue := unit ;
    hidden_init := tt;
    attribute_interpretation := fun a h args => None ;
    method_interpretation := fun m h args => None ;
    hidden_predicate_interpretation := fun p h args => None ;
|}.

Definition bindings (P HP F A Q M : Type)
    :
    string -> SymbolInfo P HP F A Q M
:=
fun s =>
match s with
| _ => si_none _ _ _ _ _ _
end.

