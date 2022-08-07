open Parser
open Pos
open Typing
open Output

let _ = Printexc.record_backtrace true
let _ = Sys.catch_break true

(* Command line argument parsing. *)
let files =
  let files = ref [] in

  let anon_fun fn = files := fn :: !files in
  let usage_msg =
    Printf.sprintf "Usage: %s [args] [f1.pml] ... [fn.pml]" Sys.argv.(0)
  in

  let show_config () =
    Printf.printf "The PML library search path contains:\n%!";
    List.iter (Printf.printf " - %S\n%!") Config.path
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
      , Arg.Tuple [Arg.Set timed]
      , " Display a timing report after the execution.")
    ; ( "--recompile"
      , Arg.Set recompile
      , " Force compilation of files given on command line.")
    ; ( "--quiet"
      , Arg.Unit(fun ()-> verbose:= Quiet)
      , " Disables the printing definition data.")
    ; ( "--silent"
      , Arg.Unit(fun ()-> verbose:= Silent)
      , " Disables all printing.")
    ; ( "--config"
      , Arg.Unit(show_config)
      , " Prints local configuration." )
    ; ( "--auto"
      , Typing. (
        Arg.Tuple [Arg.Int (fun n -> default_auto_lvl.c <- n)
                  ;Arg.Int (fun n -> default_auto_lvl.t <- n)
                  ;Arg.Int (fun n -> default_auto_lvl.d <- n)
      ])
      , " Set the default level for automatic theorem proving. Two naturals: \
          maximum number of nested case analysis and number of let statement \
          for totality.")
    ; ( "--keep-intermediate"
      , Arg.Set Equiv.keep_intermediate
      , " Keep intermediate terms in normalisation in the pool \
          (more complete, yet to prove ? but slower).")
    ; ( "--no-eval"
      , Arg.Clear Equiv.use_eval
      , " ignore try_eval keyword and to not use eval for type-checking.")
    ; ( "--no-memo"
      , Arg.Clear Typing.use_memo
      , " do not use memo when type_checking (for debugging pml only).")
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
  let rec print_exn last = function
  | Type_error(E(_,t),c,exc) ->
     if has_pos t.pos && t.pos <> last then err_msg "%a" print_err_pos t.pos;
     err_msg "Type error: %a expected." Print.ex c;
     print_exn t.pos exc
  | Typing.Subtype_error(t,a,b,exc) ->
     if has_pos t.pos && t.pos <> last  then err_msg "%a" print_err_pos t.pos;
     err_msg "Subtype error: %a ⊂ %a" Print.ex a Print.ex b;
     print_exn t.pos exc
  | Typing.Loops(t) ->
     if has_pos t.pos && t.pos <> last  then err_msg "%a" print_err_pos t.pos;
     err_msg "Cannot prove termination."
  | Typing.Subtype_msg(p,msg) ->
     if has_pos p && p <> last  then err_msg "%a" print_err_pos p;
     err_msg "Subtype error: %s." msg
  | Typing.Cannot_unify(a,b) ->
     err_msg "Unable to unify %a and %a." Print.ex a Print.ex b
  | Typing.Reachable            ->
     err_msg "Reachable scissors"
  | Equiv.Failed_to_prove(rel,_)  ->
     err_msg "Failed to prove an equational relation.";
     err_msg "  %a" Print.rel rel
  | Parser.Unexpected_success(id) ->
     err_msg "A definition that should not type-check is accepted for";
     err_msg "  %s at %a" id.elt print_err_pos id.pos;
  | Typing.Bad_delim(t,msg) ->
     err_msg "%s" msg;
     err_msg "  %a at %a" Print.ex t print_err_pos t.pos;
  | Typing.Bad_subtyping(p) ->
     err_msg "This is not a subtyping proposition";
     err_msg "  %a at %a" Print.ex p print_err_pos p.pos;
  | No_typing_IH(id)             ->
     if has_pos id.pos then err_msg "%a" print_err_pos id.pos;
     err_msg "No typing induction hypothesis for %S." id.elt;
  | No_subtyping_IH(id1, id2)    ->
     if has_pos id1.pos then err_msg "at %a" print_err_pos id1.pos;
     if has_pos id2.pos then err_msg "and at %a" print_err_pos id2.pos;
     err_msg "No subtyping induction hypothesis applies for %S < %S."
       id1.elt id2.elt;
  | Illegal_effect(e)         ->
     err_msg "Effect %a is not legal here." Effect.print e;
  | e ->
      err_msg "Unexpected exception [%s]." (Printexc.to_string e);
      err_msg "%t" Printexc.print_backtrace;
  in
  try List.iter (handle_file true) files with
  | e -> print_exn Pos.phantom_pos e; exit 1


let _ =
  let total = ref 0.0 in
  if !timed then
    begin
      Printf.eprintf   "%10s   %8s  %8s %8s\n" "name" "self" "cumul" "count";
      let f name time cumul c =
        total := !total +. time;
        Printf.eprintf "%10s: %8.2fs %8.2fs %8d\n" name time cumul c
      in
      Chrono.iter f;
      Printf.eprintf "%10s: %8.2fs\n" "total" !total
    end
