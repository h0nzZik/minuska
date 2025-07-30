From Minuska Require Import
    prelude
    spec
.

Record BasicTypesMorphism'
  {A_Var A_Ts A_Fs A_Ps A_Hps A_As A_Ms A_Qs A_BV A_HV A_NV : Type}
  {B_Var B_Ts B_Fs B_Ps B_Hps B_As B_Ms B_Qs B_BV B_HV B_NV : Type}
:= {
    Variabl_morph : A_Var -> B_Var ;
    TermSymbol_morph : A_Ts -> B_Ts ;
    FunSymbol_morph : A_Fs -> B_Fs ;
    PredSymbol_morph : A_Ps -> B_Ps ;
    HPredSymbol_morph : A_Hps -> B_Hps ;
    AttrSymbol_morph : A_As -> B_As ;
    MethSymbol_morph : A_Ms -> B_Ms ;
    QuerySymbol_morph : A_Qs -> B_Qs ;
    BasicValue_morph : A_BV -> B_BV ;
    HiddenValue_morph : A_HV -> B_HV ;
    NondetValue_morph : A_NV -> B_NV ;
}.

Definition BasicTypesMorphism
  (A B : BasicTypes)
:=
  @BasicTypesMorphism'
    A.(Variabl) A.(TermSymbol) A.(FunSymbol) A.(PredSymbol) A.(HPredSymbol) A.(AttrSymbol) A.(MethSymbol) A.(QuerySymbol) A.(BasicValue) A.(HiddenValue) A.(NondetValue)
    B.(Variabl) B.(TermSymbol) B.(FunSymbol) B.(PredSymbol) B.(HPredSymbol) B.(AttrSymbol) B.(MethSymbol) B.(QuerySymbol) B.(BasicValue) B.(HiddenValue) B.(NondetValue)
.

Class BasicTypesInjMorphism
  (A B : BasicTypes)
  (μ : BasicTypesMorphism A B)
:= {
    Variabl_morph_inj : Inj (=) (=) μ.(Variabl_morph);
    TermSymbol_morph_inj : Inj (=) (=) μ.(TermSymbol_morph);
    FunSymbol_morph_inj : Inj (=) (=) μ.(FunSymbol_morph);
    PredSymbol_morph_inj : Inj (=) (=) μ.(PredSymbol_morph);
    HPredSymbol_morph_inj : Inj (=) (=) μ.(HPredSymbol_morph);
    AttrSymbol_morph_inj : Inj (=) (=) μ.(AttrSymbol_morph);
    MethSymbol_morph_inj : Inj (=) (=) μ.(MethSymbol_morph);
    QuerySymbol_morph_inj : Inj (=) (=) μ.(QuerySymbol_morph);
    BasicValue_morph_inj : Inj (=) (=) μ.(BasicValue_morph);
    HiddenValue_morph_inj : Inj (=) (=) μ.(HiddenValue_morph);
    NondetValue_morph_inj : Inj (=) (=) μ.(NondetValue_morph);
}.

