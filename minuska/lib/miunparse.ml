open Core


let mymap (f : 'a -> 'b) (g : 'b -> 'b) (l : 'a list)  : 'b list =
    let ln = List.length l in
    List.mapi ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (g (f x))) l


let rec groundterm_to_string (g : Syntax.groundterm) : string =
  match g with
  | `GTerm (`Id s, gs) ->
    s ^ "[" ^ (String.concat (mymap groundterm_to_string (fun x -> x ^ ", ") gs)) ^ "]"

