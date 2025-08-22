module BasicTypes = struct

  type ('t, 'a) termOver =
  | T_over of 'a
  | T_term of 't * ('t, 'a) termOver list


  type 'a countable = { encode : ('a -> Big_int_Z.big_int);
                        decode : (Big_int_Z.big_int -> 'a option) }


  type 't eDC = { eqdec : 't -> 't -> bool; count : 't countable }

  type 'a infinite = 'a list -> 'a

end

module type MinuskaI = sig

  (* background model *)
  type ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8, 'a9, 'a10, 'a11, 'a12) bgModel

  (* rewriting rules *)
  type ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule

  (* basic interpreter *)
  val interpreter :
    'a1 eDC ->
    'a2 eDC ->
    'a3 eDC ->
    'a4 eDC ->
    'a4 infinite ->
    'a5 eDC ->
    'a6 eDC ->
    'a7 eDC ->
    'a8 eDC ->
    'a9 eDC ->
    'a10 eDC ->
    'a11 eDC ->
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8, 'a9, 'a10, 'a11, 'a12) bgModel ->
    ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule list ->
    'a12 ->
    'a3 ->
    (('a5, 'a1) termOver' * 'a2) ->
    (('a5, 'a1) termOver' * 'a2) option

  (* extended interpreter (returning debugging information) *)
  val interpreter_ext :
    'a1 eDC ->
    'a2 eDC ->
    'a3 eDC ->
    'a4 eDC ->
    'a4 infinite ->
    'a5 eDC ->
    'a6 eDC ->
    'a7 eDC ->
    'a8 eDC ->
    'a9 eDC ->
    'a10 eDC ->
    'a11 eDC ->
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8, 'a9, 'a10, 'a11, 'a12) bgModel ->
    ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule list ->
    'a12 ->
    'a3 ->
    (('a5, 'a1) termOver' * 'a2) ->
    ((('a5, 'a1) termOver' * 'a2) * Big_int_Z.big_int) option

end


module type BackgroundI = sig

  type variabl
  type value
  type nondet_value
  type hidden_value
  type program
  type term_symbol
  type function_symbol
  type predicate_symbol
  type hidden_predicate_symbol
  type query_symbol
  type attribute_symbol
  type method_symbol

  val variabl_edc      : variabl      BasicTypes.eDC
  val variabl_inf      : variabl      BasicTypes.infinite
  val value_edc        : value        BasicTypes.eDC
  val hidden_value_edc : hidden_value BasicTypes.eDC
  (**val program_edc      : program      BasicTypes.eDC*) (*Programs do not need to have decidable equality*)
  val term_symbol_edc  : term_symbol  BasicTypes.eDC
  val function_symbol_edc : function_symbol BasicTypes.eDC
  val predicate_symbol_edc    : predicate_symbol BasicTypes.eDC
  val hidden_predicate_symbol_edc : hidden_predicate_symbol BasicTypes.eDC
  val query_symbol_edc         : query_symbol BasicTypes.eDC
  val attribute_symbol_edc      : attribute_symbol BasicTypes.eDC
  val method_symbol_edc         : method_symbol BasicTypes.eDC

    background_model  : (('v, 'hv, 'nv, 'vr, 'ts, 'fs, 'ps, 'ats, 'ms, 'qs, 'hps, 'prg) Extracted.backgroundModelOver) ;
    builtin_inject    : (builtin_repr -> 'v) ;
    builtin_eject     : ('v -> builtin_repr ) ;
    bindings          : (string -> ('ps, 'hps,'fs,'ats,'qs,'ms) Extracted.symbolInfo) ;



end
