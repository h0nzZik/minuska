module BasicTypes = struct

  type ('t, 'a) termOver' =
  | T_over of 'a
  | T_term of 't * ('t, 'a) termOver' list


  type 'a countable = { encode : ('a -> Big_int_Z.big_int);
                        decode : (Big_int_Z.big_int -> 'a option) }


  type 't eDC = { eqdec : 't -> 't -> bool; count : 't countable }

  type 'a infinite = 'a list -> 'a

end

module type MinuskaI = sig

  type 'a countable

  type 't eDC

  type 'a infinite

  type ('t, 'a) termOver'

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


end
