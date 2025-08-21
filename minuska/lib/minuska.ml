open Libminuskapluginbase
open Pluginbase

open Coqminuskai

module Minuska : MinuskaI = struct
  type 'a countable = 'a Extracted.countable
  type 'a eDC = 'a Extracted.eDC
  type 'a infinite = 'a Extracted.infinite
  type ('a,'b) termOver' = ('a,'b) Extracted.termOver'
  type ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11) rewRule =  ('a1, 'a4, 'a5, 'a6, 'a10, 'a8, 'a9, 'a7, 'a11, Extracted.label) Extracted.rewritingRule2'
  type ('x1,'x2,'x3,'x4,'x5,'x6,'x7,'x8,'x9,'x10,'x11,'x12) bgModel = ('x1,'x2,'x3,'x4,'x5,'x6,'x7,'x8,'x9,'x10,'x11,'x12) Extracted.backgroundModelOver
  let interpreter = Extracted.top_poly_interpreter
  let interpreter_ext = Extracted.top_poly_interpreter_ext
end

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
