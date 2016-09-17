open Blank
open Tokens
open Parser

let _ =
  if Array.length Sys.argv < 2 then exit 0;
  let l = Decap.parse_file (parser toplevel*) blank Sys.argv.(1) in
  let show (name, s) =
    Printf.printf "Sort %S defined as \"%a\"\n%!" name print_sort s
  in
  List.iter show l
