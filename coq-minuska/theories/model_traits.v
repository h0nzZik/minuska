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

Class WithListTrait (Inner : Type) (Carrier : Type)
:= {
    wlt_inject_inner : Inner -> Carrier ;
    wlt_inject_inner__injective :: Inj (=) (=) wlt_inject_inner ;
    
    wlt_inject_list : list Inner -> Carrier ;
    wlt_inject_list__injective :: Inj (=) (=) wlt_inject_list ;
}.




