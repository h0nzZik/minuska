From Coq Require Import String.

Record BuiltinsBinding := {
    bb_function_names : list (string * string) ;
}.