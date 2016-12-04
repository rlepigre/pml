open Bindlib
open Blank
open Parser
open Pos
open Raw
open Typing

let interpret : Env.env -> Raw.toplevel -> Env.env = fun env top ->
  match top with
  | Sort_def(id,s) ->
      let open Env in
      let Sort s = unsugar_sort env s in
      Printf.printf "sort %s ≔ %a\n%!" id.elt Print.print_sort s;
      add_sort id.elt s env
  | Expr_def(id,s,e) ->
      let open Env in
      let Box(s,e) = unsugar_expr env e s in
      Printf.printf "expr %s : %a ≔ %a\n%!" id.elt
        Print.print_sort s Print.print_ex (Bindlib.unbox e);
      add_expr id.elt s e env
  | Valu_def(id,ao,t) ->
      let open Env in
      let ao =
        match ao with
        | None   -> None
        | Some a -> Some(unbox (to_prop (unsugar_expr env a _sp)))
      in
      let t = unbox (to_term (unsugar_expr env t _st)) in
      let prf = type_check t ao in
      ignore prf; env (* TODO *)

let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m"

let ast =
  if Array.length Sys.argv <> 2 then
    begin
      Printf.eprintf "Usage: %s <file.pml>\n%!" Sys.argv.(0);
      exit 1
    end;
  try Parser.parse_file Sys.argv.(1) with
  | Sys_error(_) ->
      begin
        Printf.eprintf ((red "File %s does not exist.") ^^ "\n%!")
          Sys.argv.(1);
        exit 1
      end

let _ =
  try List.fold_left interpret Env.empty ast with
  | Unbound_sort(s, None  ) ->
      begin
        Printf.eprintf (red "Unbound sort %s.\n%!") s;
        exit 1
      end
  | Unbound_sort(s, Some p) ->
      begin
        Printf.eprintf ((red "Unbound sort %s") ^^ " (%a).\n%!") s
          Pos.print_pos p;
        exit 1
      end
