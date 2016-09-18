open Blank
open Parser
open Pos
open Raw

let _ =
  if Array.length Sys.argv < 2 then exit 0;
  let l = Decap.parse_file (parser toplevel*) blank Sys.argv.(1) in
  let show = function
    | Sort_def(id,s) ->
        Printf.printf "Sort %S defined as \"%a\"\n%!" id.elt Raw.Sort.print s
    | Expr_def(id,args,s,e) ->
        Printf.printf "Expr %S defined as ...\n%!" id.elt
  in
  List.iter show l
