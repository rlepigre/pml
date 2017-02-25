open Bindlib
open Blank
open Parser
open Pos
open Raw
open Typing
open Output
open Eval

let interpret : Env.env -> Raw.toplevel -> Env.env = fun env top ->
  match top with
  | Sort_def(id,s) ->
      let open Env in
      let Sort s = unsugar_sort env s in
      out "sort %s ≔ %a\n%!" id.elt Print.sort s;
      add_sort id.elt s env
  | Expr_def(id,s,e) ->
      let open Env in
      let Box(s,e) = unsugar_expr env e s in
      let ee = Bindlib.unbox e in
      out "expr %s : %a ≔ %a\n%!" id.elt Print.sort s Print.ex ee;
      add_expr id s e env
  | Valu_def(id,ao,t) ->
      let open Env in
      let ao =
        match ao with
        | None   -> None
        | Some a -> Some(unbox (to_prop (unsugar_expr env a _sp)))
      in
      let t = unbox (to_term (unsugar_expr env t _st)) in
      let (a, prf) = type_check t ao in
      let v = Eval.eval (Erase.term_erasure t) in
      out "val %s : %a\n%!" id.elt Print.ex a;
      out "  = %a\n%!" Print.print_ex (Erase.to_valu v);
      ignore prf;
      add_value id t a v env

(* Command line argument parsing. *)
let files =
  let files = ref [] in

  let anon_fun fn = files := fn :: !files in
  let usage_msg =
    Printf.sprintf "Usage: %s [args] [f1.pml] ... [fn.pml]" Sys.argv.(0)
  in

  let r_spec = ref [] in
  let help f =
    let act () = raise (Arg.Help (Arg.usage_string !r_spec usage_msg)) in
    (f, Arg.Unit(act), " Show this usage message.")
  in

  let spec =
    [ ( "--log-file"
      , Arg.String(Log.with_file)
      , "file Write logs to the provided file." )
    ; ( "--log"
      , Arg.String(Log.set_enabled)
      , Printf.sprintf "str Enable the provided logs. Available options:\n%s."
          (Log.opts_to_string ((String.make 20 ' ') ^ "- ")) )
    ; ( "--full-terms"
      , Arg.Set Print.print_full
      , " Fully display terms (including the definition of witnesses)." )
    ; ( "--full-compare"
      , Arg.Set Compare.full_eq
      , " Show all the steps when comparing expressions.")
    ] @ List.map help ["--help" ; "-help" ; "-h" ]
  in
  let spec = Arg.align spec in
  r_spec := spec;

  (* Run checks on files. *)
  Arg.parse spec anon_fun usage_msg;
  let files = List.rev !files in

  let check_ext fn =
    if not (Filename.check_suffix fn ".pml") then
      begin
        err_msg "File \"%s\" does not have the \".pml\" extension." fn;
        exit 1
      end
  in
  List.iter check_ext files;
  let check_exists fn =
    if not (Sys.file_exists fn) then
      begin
        err_msg "File \"%s\" does not exist." fn;
        exit 1
      end;
    if Sys.is_directory fn then
      begin
        err_msg "\"%s\" is not a file, but a directory." fn;
        exit 1
      end
  in
  List.iter check_exists files;
  files

(* Handling the files. *)
let handle_file env fn =
  out "[%s]\n%!" fn;
  try
    let ast = Parser.parse_file fn in
    List.fold_left interpret env ast
  with
  | No_parse(p, None)       ->
      begin
        err_msg "No parse %a." Pos.print_short_pos p;
        exit 1
      end
  | No_parse(p, Some msg)   ->
      begin
        err_msg "No parse %a (%s)." Pos.print_short_pos p msg;
        exit 1
      end
  | Unbound_sort(s, None  ) ->
      begin
        err_msg "Unbound sort %s." s;
        exit 1
      end
  | Unbound_sort(s, Some p) ->
      begin
        err_msg "Unbound sort %s (%a)." s Pos.print_short_pos p;
        exit 1
      end
  | Sort_clash(t,s) ->
      begin
        let _ =
          match t.pos with
          | None   -> err_msg "Sort %a expected for %a."
                        pretty_print_raw_sort s print_raw_expr t
          | Some p -> err_msg "Sort %a expected at %a."
                        pretty_print_raw_sort s Pos.print_short_pos p
        in
        exit 1
      end
  | Unbound_variable(x,p)   ->
      begin
        match p with
        | None   -> err_msg "Unbound variable %s." x;
                    exit 1
        | Some p -> err_msg "Unbound variable %s at %a." x
                      Pos.print_short_pos p;
                    exit 1
      end

let _ =
  try ignore (List.fold_left handle_file Env.empty files) with
  | Typing.Subtype_error(p,msg) ->
      begin
        match p with
        | None   -> err_msg "Subtype error: %s." msg
        | Some p -> err_msg "Subtype error in %s." (pos_to_string p);
                    err_msg "Message: %s." msg
      end
  | Typing.Type_error(p,msg)    ->
      begin
        match p with
        | None   -> err_msg "Type error: %s." msg
        | Some p -> err_msg "Type error in %s." (pos_to_string p);
                    err_msg "Message: %s." msg
      end
  | Equiv.Failed_to_prove(rel)  ->
      err_msg "Failed to prove an equational relation.";
      err_msg "  %a" Equiv.print_relation_pos rel
  | e -> err_msg "Uncaught exception [%s]." (Printexc.to_string e)
