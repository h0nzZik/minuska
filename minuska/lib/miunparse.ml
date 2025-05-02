open Core
open Libminuskapluginbase
open Pluginbase

let mymap (f : 'a -> 'b) (g : 'b -> 'b) (l : 'a list)  : 'b list =
    let ln = List.length l in
    List.mapi ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (g (f x))) l


let builtin_to_string (pvae : primitiveValueAlgebraEntry) (b : builtin_repr) : string =
  match (b) with 
  | {br_kind=k; br_value=v;} -> (sprintf "(@builtin:%s(%s))" k v)

let rec groundterm_to_string (pvae : primitiveValueAlgebraEntry) (g : Syntax.groundterm) : string =
  match g with
  | `GTb b -> "[" ^ (builtin_to_string pvae b) ^ "]"
  | `GTerm (`Id s, gs) ->
    s ^ "[" ^ (String.concat (mymap (groundterm_to_string pvae) (fun x -> x ^ ", ") gs)) ^ "]"

