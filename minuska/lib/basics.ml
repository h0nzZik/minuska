module BasicTypes = struct

  type builtin_repr = {
    br_kind : string ;
    br_value : string;
  }

  type ('t, 'a) termOver =
  | T_over of 'a
  | T_term of 't * ('t, 'a) termOver list


  type 'a countable = { encode : ('a -> Big_int_Z.big_int);
                        decode : (Big_int_Z.big_int -> 'a option); }


  type 't eDC = { eqdec : 't -> 't -> bool; count : 't countable; }

  type 'a infinite = 'a list -> 'a


  type ('p, 'hp, 'f, 'a, 'q, 'm) symbolInfo =
  | Si_none
  | Si_predicate of 'p
  | Si_hidden_predicate of 'hp
  | Si_function of 'f
  | Si_attribute of 'a
  | Si_query of 'q
  | Si_method of 'm

  type ('v, 'nv, 'sy, 'fs, 'ps) visibleAlgebra = {
    interp_function : 'fs -> 'nv -> ('sy, 'v) termOver list -> ('sy, 'v) termOver option;
    interp_predicate : 'ps -> 'nv -> ('sy, 'v) termOver list -> bool option;
    }


  type ('v, 'hv, 'nv, 'sy, 'ats, 'ms, 'hps) hiddenAlgebra = {
    interp_attribute : 'ats -> 'hv -> ('sy, 'v) termOver list -> 'v option ;
    interp_method : 'ms -> 'hv -> ('sy,'v) termOver list -> 'hv option;
    interp_hidden_predicate : 'hps -> 'hv -> ('sy, 'v) termOver list -> bool option;
    init_hidden : 'hv ;
    }

  type ('prog, 'v, 'sy, 'qs) programInfo = {
    query_program : 'prog -> 'qs -> ('sy, 'v) termOver list -> ('sy, 'v) termOver option ;
    }

  type ('v, 'hv, 'nv, 'va, 'sy, 'fs, 'ps, 'ats, 'ms, 'qs, 'hps, 'prog) bgModel = {
    visible : ('v, 'nv, 'sy, 'fs, 'ps) visibleAlgebra ;
    hidden : ('v, 'hv, 'nv, 'sy, 'ats, 'ms, 'hps) hiddenAlgebra ;
    program : ('prog, 'v, 'sy, 'qs) programInfo ;
    }

end

module type MinuskaI = sig

  (* background model *)
  type ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8, 'a9, 'a10, 'a11, 'a12) bgModel

  (* rewriting rules *)
  type ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule

  (* basic interpreter *)
  val interpreter :
    'a1 BasicTypes.eDC ->
    'a2 BasicTypes.eDC ->
    'a3 BasicTypes.eDC ->
    'a4 BasicTypes.eDC ->
    'a4 BasicTypes.infinite ->
    'a5 BasicTypes.eDC ->
    'a6 BasicTypes.eDC ->
    'a7 BasicTypes.eDC ->
    'a8 BasicTypes.eDC ->
    'a9 BasicTypes.eDC ->
    'a10 BasicTypes.eDC ->
    'a11 BasicTypes.eDC ->
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8, 'a9, 'a10, 'a11, 'a12) bgModel ->
    ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule list ->
    'a12 ->
    'a3 ->
    (('a5, 'a1) BasicTypes.termOver * 'a2) ->
    (('a5, 'a1) BasicTypes.termOver * 'a2) option

  (* extended interpreter (returning debugging information) *)
  val interpreter_ext :
    'a1 BasicTypes.eDC ->
    'a2 BasicTypes.eDC ->
    'a3 BasicTypes.eDC ->
    'a4 BasicTypes.eDC ->
    'a4 BasicTypes.infinite ->
    'a5 BasicTypes.eDC ->
    'a6 BasicTypes.eDC ->
    'a7 BasicTypes.eDC ->
    'a8 BasicTypes.eDC ->
    'a9 BasicTypes.eDC ->
    'a10 BasicTypes.eDC ->
    'a11 BasicTypes.eDC ->
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8, 'a9, 'a10, 'a11, 'a12) bgModel ->
    ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule list ->
    'a12 ->
    'a3 ->
    (('a5, 'a1) BasicTypes.termOver * 'a2) ->
    ((('a5, 'a1) BasicTypes.termOver * 'a2) * Big_int_Z.big_int) option

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

  val bg_model :
    (value,
     hidden_value,
     nondet_value,
     variabl,
     term_symbol,
     function_symbol,
     predicate_symbol,
     attribute_symbol,
     method_symbol,
     query_symbol,
     hidden_predicate_symbol,
     program
    ) BasicTypes.bgModel

  val builtin_inject : BasicTypes.builtin_repr -> value
  val builtin_eject : value -> BasicTypes.builtin_repr
  val bindings :
    string ->
    (predicate_symbol,
     hidden_predicate_symbol,
     function_symbol,
     attribute_symbol,
     query_symbol,
     method_symbol
    ) BasicTypes.symbolInfo

end
