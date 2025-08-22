(* Implements Minuska OCaml interface using the sources of Minuska extracted from Coq   *)
open Libminuskapluginbase
open Pluginbase

open Basics


let back_countable : 'a Extracted.countable -> 'a BasicTypes.countable =
  fun x ->
  match x with
  | { Extracted.encode = y; Extracted.decode = z; } ->
     { BasicTypes.encode = y; BasicTypes.decode = z; }

let forth_countable : 'a BasicTypes.countable -> 'a Extracted.countable =
  fun x ->
  match x with
  | { BasicTypes.encode = y; BasicTypes.decode = z; } ->
     { Extracted.encode = y; Extracted.decode = z; }


let back_edc : 'a Extracted.eDC -> 'a BasicTypes.eDC =
  fun x ->
  match x with
  | { Extracted.edc_eqdec = y; Extracted.edc_count = z; } ->
     { BasicTypes.eqdec = y; BasicTypes.count = back_countable z; }

let forth_edc : 'a BasicTypes.eDC -> 'a Extracted.eDC =
  fun x ->
  match x with
  | { BasicTypes.eqdec = y; BasicTypes.count = z; } ->
     { Extracted.edc_eqdec = y; Extracted.edc_count = forth_countable z; }


let back_infinite : 'a Extracted.infinite -> 'a BasicTypes.infinite =
  fun x -> x

let forth_infinite : 'a BasicTypes.infinite -> 'a Extracted.infinite =
  fun x -> x


let rec back_to : ('a,'b) Extracted.termOver' -> ('a,'b) BasicTypes.termOver =
  fun x ->
  match x with
  | Extracted.T_over y -> BasicTypes.T_over y
  | Extracted.T_term (s, l) -> BasicTypes.T_term (s, (List.map back_to l))

let rec forth_to : ('a,'b) BasicTypes.termOver -> ('a,'b) Extracted.termOver' =
  fun x ->
  match x with
  | BasicTypes.T_over y -> Extracted.T_over y
  | BasicTypes.T_term (s, l) -> Extracted.T_term (s, (List.map forth_to l))

module Minuska : MinuskaI = struct
  type 'a countable = 'a Extracted.countable
  type 'a eDC = 'a Extracted.eDC
  type 'a infinite = 'a Extracted.infinite
  type ('a,'b) termOver' = ('a,'b) Extracted.termOver'
  type ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule =  ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11, Extracted.label) Extracted.rewritingRule2'
  type ('x1,'x2,'x3,'x4,'x5,'x6,'x7,'x8,'x9,'x10,'x11,'x12) bgModel = ('x1,'x2,'x3,'x4,'x5,'x6,'x7,'x8,'x9,'x10,'x11,'x12) Extracted.backgroundModelOver
  let interpreter = fun e1 e2 e3 e4 i4 e5 e6 e7 e8 e9 e10 e11 a b c d t ->
    let tmp = Extracted.top_poly_interpreter
      (forth_edc e1)
      (forth_edc e2)
      (forth_edc e3)
      (forth_edc e4)
      (forth_infinite i4)
      (forth_edc e5)
      (forth_edc e6)
      (forth_edc e7)
      (forth_edc e8)
      (forth_edc e9)
      (forth_edc e10)
      (forth_edc e11)
      a b c d
      (forth_to (fst t),(snd t)) in
    match tmp with
    | None -> None
    | Some x -> Some (back_to (fst x), snd x)

  let interpreter_ext = fun e1 e2 e3 e4 i4 e5 e6 e7 e8 e9 e10 e11 a b c d t ->
    let tmp = Extracted.top_poly_interpreter_ext
    (forth_edc e1)
      (forth_edc e2)
      (forth_edc e3)
      (forth_edc e4)
      (forth_infinite i4)
      (forth_edc e5)
      (forth_edc e6)
      (forth_edc e7)
      (forth_edc e8)
      (forth_edc e9)
      (forth_edc e10)
      (forth_edc e11)
      a b c d
      (forth_to (fst t),(snd t)) in
    match tmp with
    | None -> None
    | Some x -> Some (((back_to (fst (fst x))), snd (fst x)), snd x)

end
