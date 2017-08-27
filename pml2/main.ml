open Bindlib
open Blank
open Parser
open Pos
open Raw
open Typing
open Output
open Eval
open Config

let _ = Printexc.record_backtrace true

let verbose = ref true
let timed   = ref false

let find_file : string -> string = fun fn ->
  let add_fn dir = Filename.concat dir fn in
  let ls = fn :: (List.map add_fn path) in
  let rec find ls =
    match ls with
    | []     -> err_msg "File \"%s\" does not exist." fn; exit 1
    | fn::ls -> if Sys.file_exists fn then fn else find ls
  in find ls

let find_module : string list -> string = fun ps ->
  let fn = (String.concat "/" ps) ^ ".pml" in
  find_file fn

exception Check_failed of Ast.prop * bool * Ast.prop

let rec interpret : Env.env -> Raw.toplevel -> Env.env = fun env top ->
  match top with
  | Sort_def(id,s) ->
      let open Env in
      let Sort s = unsugar_sort env s in
      if !verbose then
        out "sort %s ≔ %a\n%!" id.elt Print.sort s;
      add_sort id.elt s env
  | Expr_def(id,s,e) ->
      let open Env in
      let Box(s,e) = unsugar_expr env e s in
      let ee = Bindlib.unbox e in
      if !verbose then
        out "expr %s : %a ≔ %a\n%!" id.elt Print.sort s Print.ex ee;
      add_expr id s e env
  | Valu_def(id,a,t) ->
      let open Env in
      let a = unbox (to_prop (unsugar_expr env a _sp)) in
      let t = unbox (to_term (unsugar_expr env t _st)) in
      let (a, prf) = type_check t a in
      let v = Eval.eval (Erase.term_erasure t) in
      if !verbose then
        out "val %s : %a\n%!" id.elt Print.ex a;
      (* out "  = %a\n%!" Print.ex (Erase.to_valu v); *)
      ignore prf;
      add_value id t a v env
  | Chck_sub(a,n,b) ->
      let open Env in
      let a = unbox (to_prop (unsugar_expr env a _sp)) in
      let b = unbox (to_prop (unsugar_expr env b _sp)) in
      if is_subtype a b <> n then raise (Check_failed(a,n,b));
      if !verbose then
        begin
          let (l,r) = if n then ("","") else ("¬(",")") in
          out "showed %s%a ⊂ %a%s\n%!" l Print.ex a Print.ex b r;
        end;
      env
  | Include(ps) ->
      let fn = find_module ps in
      if !verbose then
        out "include %S\n%!" fn;
      Log.without (handle_file env) fn

(* Handling the files. *)
and handle_file env fn =
  try
    try Env.load_file env fn with Env.Compile ->
    if !verbose then out "[%s]\n%!" fn;
    Env.start fn;
    let ast = Parser.parse_file fn in
    let env = List.fold_left interpret env ast in
    Env.save_file env fn; env
  with
  | No_parse(p, None)       ->
      begin
        err_msg "No parse %a." Pos.print_short_pos p;
        Quote.quote_file stderr p;
        exit 1
      end
  | No_parse(p, Some msg)   ->
      begin
        err_msg "No parse %a (%s)." Pos.print_short_pos p msg;
        Quote.quote_file stderr p;
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
        Quote.quote_file stderr p;
        exit 1
      end
  | Sort_clash(t,s) ->
      begin
        let _ =
          match t.pos with
          | None   -> err_msg "Sort %a expected for %a."
                        pretty_print_raw_sort s print_raw_expr t
          | Some p -> err_msg "Sort %a expected %a."
                        pretty_print_raw_sort s Pos.print_short_pos p;
                      Quote.quote_file stderr p
        in
        exit 1
      end
  | Unbound_variable(x,p)   ->
      begin
        let _ =
          match p with
          | None   -> err_msg "Unbound variable %s." x;
          | Some p -> err_msg "Unbound variable %s %a." x
                        Pos.print_short_pos p;
                      Quote.quote_file stderr p
        in
        exit 1
      end
  | Already_matched(c)      ->
      begin
        match c.pos with
        | None   -> err_msg "%s has already been matched." c.elt;
        | Some p -> err_msg "%s (%a) has already been matched." c.elt
                      Pos.print_short_pos p;
                    Quote.quote_file stderr p
      end;
      exit 1

let parsing_chrono = Chrono.create "parsing"

let handle_file = Chrono.add_time parsing_chrono handle_file

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
    ; ( "--full-compare"
      , Arg.Set Compare.full_eq
      , " Show all the steps when comparing expressions.")
    ; ( "--always-colors"
      , Arg.Set Output.always_colors
      , " Always use colors.")
    ; ( "--timed"
      , Arg.Set timed
      , " Display a timing report after the execution.")
    ; ( "--quiet"
      , Arg.Clear verbose
      , " Disables the printing definition data.")
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

let _ =
  let rec print_exn = function
  | Type_error(E(_,t),c,exc) ->
      begin
        match t.pos with
        | None   -> err_msg "Type error:\n%a : %a"
                      Print.ex t Print.ex c
        | Some p -> err_msg "Type error %a:\n%a : %a"
                      Pos.print_short_pos p Print.ex t Print.ex c;
                    Quote.quote_file stderr p
     end; print_exn exc
  | Typing.Subtype_error(t,a,b,e) ->
      begin
        match t.pos with
        | None   -> err_msg "Subtype error:\n%a ∈ %a ⊂ %a"
                      Print.ex t Print.ex a Print.ex b
        | Some p -> err_msg "SubType error %a:\n  %a ∈ %a ⊂ %a"
                      Pos.print_short_pos p Print.ex t Print.ex a Print.ex b;
                    Quote.quote_file stderr p
      end; print_exn e
  | Typing.Loops(t) ->
      begin
        match t.pos with
        | None   -> err_msg "Cannot prove termination of\n  %a" Print.ex t
        | Some p -> err_msg "Cannot prove termination.";
                    Quote.quote_file stderr p
      end
  | Typing.Subtype_msg(p,msg) ->
      begin
        match p with
        | None   -> err_msg "Subtype error:\n%s." msg
        | Some p -> err_msg "Subtype error %a:\n%s."
                      Pos.print_short_pos p msg;
                    Quote.quote_file stderr p
      end
  | Typing.Cannot_unify(a,b) ->
      err_msg "Unable to unify %a and %a." Print.ex a Print.ex b
  | Typing.Reachable            ->
      err_msg "Reachable scissors"
  | Equiv.Failed_to_prove(rel)  ->
      err_msg "Failed to prove an equational relation.";
      err_msg "  %a" Print.rel rel
  | Check_failed(a,n,b) ->
      let (l,r) = if n then ("","") else ("¬(",")") in
      err_msg "Failed to prove a subtyping relation.";
      begin
        let pp = Pos.print_short_pos in
        match (a.pos, b.pos) with
        | (Some pa, Some pb) -> err_msg "  %s(%a) ⊂ (%a)%s" l pp pa pp pb r
        | (_      , _      ) -> ()
      end;
      err_msg "  %s%a ⊂ %a%s" l Print.ex a Print.ex b r
  | e ->
      err_msg "Unexpected exception [%s]." (Printexc.to_string e);
      err_msg "%t" Printexc.print_backtrace;
  in
  try ignore (List.fold_left handle_file Env.empty files) with
  | e -> print_exn e; exit 1


let _ =
  let total = ref 0.0 in
  if !timed then
    begin
      let f name t c =
        total := !total +. t;
        Printf.eprintf "%10s: %8.2fs %8d\n" name t c
      in
      Chrono.iter f;
      Printf.eprintf "%10s: %8.2fs\n" "total" !total
    end
