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
      , Arg.Clear verbose
      , " Disables the printing definition data.")
    ; ( "--config"
      , Arg.Unit(show_config)
      , " Prints local configuration." )
    ; ( "--auto"
      , Typing. (
        Arg.Tuple [Arg.Int (fun n ->
                       default_auto_lvl := (n, snd !default_auto_lvl))
                  ;Arg.Int (fun n ->
                       default_auto_lvl := (fst !default_auto_lvl, n))
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
        if has_pos t.pos then
          err_msg "Type error %a:\n%a : %a"
            Pos.print_err_pos t.pos Print.ex t Print.ex c
        else
          err_msg "Type error:\n%a : %a"
            Print.ex t Print.ex c
     end; print_exn exc
  | Typing.Subtype_error(t,a,b,e) ->
      begin
        if has_pos t.pos then
          err_msg "SubType error %a:\n  %a ∈ %a ⊂ %a"
            Pos.print_err_pos t.pos Print.ex t Print.ex a Print.ex b
        else
          err_msg "Subtype error:\n%a ∈ %a ⊂ %a"
            Print.ex t Print.ex a Print.ex b
      end; print_exn e
  | Typing.Loops(t) ->
      begin
        if has_pos t.pos then
          err_msg "Cannot prove termination at %a." print_err_pos t.pos
        else
          err_msg "Cannot prove termination of\n  %a" Print.ex t
      end
  | Typing.Subtype_msg(p,msg) ->
      begin
        if has_pos p then
          err_msg "Subtype error %a:\n%s."
            Pos.print_err_pos p msg
        else
          err_msg "Subtype error:\n%s." msg
      end
  | Typing.Cannot_unify(a,b) ->
      err_msg "Unable to unify %a and %a." Print.ex a Print.ex b
  | Typing.Reachable            ->
      err_msg "Reachable scissors"
  | Equiv.Failed_to_prove(rel,_)  ->
      err_msg "Failed to prove an equational relation.";
      err_msg "  %a" Print.rel rel
  | Check_failed(a,n,b) ->
      let (l,r) = if n then ("","") else ("¬(",")") in
      if has_pos a.pos then err_msg "%a" print_err_pos a.pos;
      if has_pos b.pos then err_msg "%a" print_err_pos b.pos;
      err_msg "Failed to prove a subtyping relation.";
      err_msg "  %s%a ⊂ %a%s" l Print.ex a Print.ex b r;
  | No_typing_IH(id)             ->
      begin
        err_msg "No typing induction hypothesis applies for %S." id.elt;
        if has_pos id.pos then
          err_msg "at %a" print_err_pos id.pos
      end
  | No_subtyping_IH(id1, id2)    ->
      begin
        err_msg "No typing induction hypothesis applies for %S < %S."
                id1.elt id2.elt;
        if has_pos id1.pos then
          err_msg "at %a" print_err_pos id1.pos;
        if has_pos id2.pos then
          err_msg "and at %a" print_err_pos id2.pos
      end
  | Illegal_effect(e)         ->
      begin
        err_msg "Effect %a is not legal here." Effect.print e;
      end
  | e ->
      err_msg "Unexpected exception [%s]." (Printexc.to_string e);
      err_msg "%t" Printexc.print_backtrace;
  in
  try List.iter (handle_file true) files with
  | e -> print_exn e; exit 1


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
