From Minuska Require Import
    prelude
    spec
.

Class WithErrTrait (Carrier : Type)
:= {
    wet_error : Carrier ;
}.

Class WithBoolTrait (Carrier : Type)
:= {
    wbt_inject_bool : bool -> Carrier ;
    wbt_inject_bool__injective :: Inj (=) (=) wbt_inject_bool ;
}.

Class WithIntTrait (Carrier : Type)
:= {
    wit_inject_Z : Z -> Carrier ;
    wit_inject_Z__injective :: Inj (=) (=) wit_inject_Z ;
}.
