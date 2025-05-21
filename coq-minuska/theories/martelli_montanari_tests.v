From Minuska Require Import
    spec
    empty
    trivial
    default_everything
    martelli_montanari
.

(*
These examples are taken directly from the
Haskell implementation test suite. The Coq
results differ, but are equivalent. This
is caused by different picking of elements
between the implementations. However, the
resulting mgus of both implementation should
be directly equal.

The first test is a proof of concept, and the
second is a sanity check. More tests are pointless,
because, any mistakes will inherently be found out
during the proving of the rest of the implementation.
*)

Instance sm : StaticModel := @DSM mysignature β MyProgramInfo.

Definition dec_paper_input1 : list (TermOver BuiltinOrVar) := [
    t_term "f"
        [
            t_over (bov_variable "x1");
            t_term "g"
                [t_term "a" [];
                    t_term "f"
                        [ t_over (bov_variable "x5"); t_term "b" [] ]
                ]
        ];
    t_term "f"
        [
            t_term "h"
                [ t_term "c" [] ];
            t_term "g"
                [t_over (bov_variable "x2");
                    t_term "f"
                        [ t_term "b" []; t_over (bov_variable "x5") ]
                ]
        ];
    t_term "f"
        [
            t_term "h"
                [ t_over (bov_variable "x4") ];
            t_term "g"
                [t_over (bov_variable "x6");
                 t_over (bov_variable "x3")
                ]
        ]
    ]
.

(* This test primarily shows that TermOver_size is enough on a example. *)

Compute (@dec sm dec_paper_input1).

Definition unify_paper1_input1 : TermOver BuiltinOrVar := (t_term "f" [
  t_over (bov_variable "x1");
  t_term "g" [t_over (bov_variable "x2"); t_over (bov_variable "x3")];
  t_over (bov_variable "x2");
  t_term "b" []]).
Definition unify_paper1_input2 : TermOver BuiltinOrVar := (t_term "f" [
  t_term "g" [t_term "h" [t_term "a" []; t_over (bov_variable "x5")]; t_over (bov_variable "x2")];
  t_over (bov_variable "x1");
  t_term "h" [t_term "a" []; t_over (bov_variable "x4")];
  t_over (bov_variable "x4")]).

(*
Expected result for the last example is:

"0" -> [t_term "f"
              [
                t_over (bov_variable "x1");
                t_over (bov_variable "x1");
                t_over (bov_variable "x2");
                t_over (bov_variable "x4")
              ]
      ]
"x4" -> [t_term "b" []]
"x2" -> [t_term "h" [t_term "a" []; t_term "b" []]]
"x1" -> [t_term "g"
              [t_term "h" [
                            t_term "a" []; 
                            t_over (bov_variable "x5")
                          ];
               t_over (bov_variable "x3")
              ]
        ]
"x5" -> [t_term "b" []]
"x3" -> [t_term "h" [t_term "a" []; t_term "b" []]]
*)

Compute (@unify_terms sm U_listset_ops [unify_paper1_input1; unify_paper1_input2]).


Definition mgu_res := 
  match (@unify_terms sm U_listset_ops [unify_paper1_input1; unify_paper1_input2]) with
    | Some t => Some (extract_mgu t)
    | None => None
  end
.

(*
Expected result:
"0"  -> t_term "f" [t_term "g" [
                                t_term "h" [
                                            t_term "a" [];t_term "b" []
                                           ];
                                t_term "h" [
                                            t_term "a" [];
                                            t_term "b" []
                                           ]
                              ];
                  t_term "g" [
                                t_term "h" [
                                            t_term "a" [];
                                            t_term "b" []
                                           ];
                                t_term "h" [
                                            t_term "a" [];
                                            t_term "b" []
                                           ]
                              ];
                  t_term "h" [
                              t_term "a" [];
                              t_term "b" []
                             ];
                  t_term "b" []
                  ]
"x1" -> t_term "g" [t_term "h" [
                                t_term "a" [];
                                t_term "b" []
                               ];
                    t_term "h" [
                                t_term "a" [];
                                t_term "b" []
                               ]
                   ];
"x2" -> t_term "h" [t_term "a" [];t_term "b" []]);
"x3" -> t_term "h" [t_term "a" [];t_term "b" []]);
"x4" -> t_term "b" []);
"x5" -> t_term "b" [])]
 *)
Compute mgu_res.
