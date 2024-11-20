open Core


let ascii_to_char = (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Stdlib.Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7)
)

let char_to_ascii = (fun c ->
  let n = Stdlib.Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  Dsm.Ascii ((h 0), (h 1), (h 2), (h 3), (h 4), (h 5), (h 6), (h 7)))

let rec ascii_list_to_string l =
  match l with
  | [] -> Dsm.EmptyString
  | x::xs -> Dsm.String (x, (ascii_list_to_string xs))

let rec dsmString_to_ascii_list s =
  match s with
  | Dsm.EmptyString -> []
  | Dsm.String (x, xs) -> x::(dsmString_to_ascii_list xs)

let explode' s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  (exp (String.length s - 1) [])

let explode s : Dsm.string = ascii_list_to_string (List.map ~f:(char_to_ascii) (explode' s))

let destrut_ascii a =
  match a with
  | Dsm.Ascii (b1,b2,b3,b4,b5,b6,b7,b8) ->
    (b1,b2,b3,b4,b5,b6,b7,b8)

let string_of_chars chars = 
  let buf = Buffer.create 16 in
  List.iter ~f:(Buffer.add_char buf) chars;
  Buffer.contents buf

let implode (s : Dsm.string) : string =
  let l2 = dsmString_to_ascii_list s in
  let l3 = List.map ~f:destrut_ascii l2 in
  let l4 = List.map ~f:(ascii_to_char) l3 in
  string_of_chars l4

