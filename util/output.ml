(** A very simple module providing colorfull output facilities for logs  (or
    log file), warnings and errors. Support is provided for integration with
    command line arguments parsing. *)

(* Type of a printf-like function. *)
type 'a printer = ('a, out_channel, unit) format -> 'a

(* Main printing function (to standard output). *)
let out : 'a printer =
  Printf.printf

(* Test if a channel corresponds to a terminal. *)
let isatty : out_channel -> bool =
  fun ch -> Unix.isatty (Unix.descr_of_out_channel ch)

let format_from_string str =
  Scanf.format_from_string str ""

(* Color modifiers. *)
let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m"

(* Printing function for a warning message. *)
let wrn_msg : 'a printer =
  fun fmt ->
    let fmt = "[WRN] " ^^ fmt ^^ "\n%!" in
    let fmt = if isatty stderr then yel fmt else fmt in
    Printf.eprintf fmt

(* Printing function for an error message. *)
let err_msg : 'a printer =
  fun fmt ->
    let fmt = "[ERR] " ^^ fmt ^^ "\n%!" in
    let fmt = if isatty stderr then red fmt else fmt in
    Printf.eprintf fmt

(* Printing function for a bug signaling message. *)
let bug_msg : 'a printer =
  fun fmt ->
    let fmt = "[BUG] " ^^ fmt ^^ "\n%!" in
    let fmt = if isatty stderr then mag fmt else fmt in
    Printf.eprintf fmt

module Log =
  struct
    (* Character map and set modules. *)
    module CMap = Map.Make(Char)
    module CSet = Set.Make(Char)

    (* Log channel. *)
    let log_channel = ref stderr
    
    (* Write the log in the given file. *)
    let with_file : string -> unit =
      fun fname ->
        let ch = open_out fname in
        log_channel := ch;
        at_exit (fun () -> close_out ch)

    (* Write the log to the given channel. *)
    let with_out_channel : out_channel -> unit =
      fun ch -> log_channel := ch

    (* Write to the log unconditionally. *)
    let log : ?tag:string -> 'a printer =
      fun ?(tag="log") fmt ->
        if String.length tag <> 3 then
          wrn_msg "the tag is too long (Output.Log.log)\n%!";
        let tag = format_from_string (Printf.sprintf "[%s] " tag) in
        let tag = if isatty !log_channel then cya tag else tag in
        Printf.fprintf !log_channel (tag ^^ fmt ^^ "\n%!")
    
    let valid   : CSet.t ref               = ref CSet.empty
    let enabled : CSet.t ref               = ref CSet.empty
    let descr   : string CMap.t ref        = ref CMap.empty
    let tags    : string option CMap.t ref = ref CMap.empty
    
    (* Enable logs with the given key. *)
    let enable : char -> unit =
      fun c ->
        if not (CSet.mem c !valid) then
          wrn_msg "no registered log with key \'%c\' (Output.Log.enable)\n" c
        else
          enabled := CSet.add c !enabled
    
    (* Disable logs with the given key. *)
    let disable : char -> unit =
      fun c -> enabled := CSet.remove c !enabled
    
    (* Set the enabled logs. *)
    let set_enabled : string -> unit =
      fun str ->
        enabled := CSet.empty;
        String.iter enable str

    type r_printer = { printer : 'a. 'a printer } 
    
    let register : char -> string option -> string -> r_printer =
      fun key tag desc ->
        valid := CSet.add key !valid;
        descr := CMap.add key desc !descr;
        tags  := CMap.add key tag !tags;  
        let tag =
          match tag with
          | None     -> "log"
          | Some tag -> tag
        in
        if String.length tag <> 3 then
          wrn_msg "the tag is too long (Output.Log.register)\n%!";
        let printer fmt =
          let tag = format_from_string (Printf.sprintf "[%s] " tag) in
          let tag = if isatty !log_channel then cya tag else tag in
          let fmt = tag ^^ fmt ^^ "\n%!" in
          if CSet.mem key !enabled then
            Printf.fprintf !log_channel fmt
          else
            Printf.ifprintf !log_channel fmt
        in
        { printer }

    (* Register a new log function. *)
    let register : char -> string option -> string -> 'a printer =
      fun key tag desc -> (register key tag desc).printer
    
    (* Show the list of the registered logs. *)
    let print_opts : ?prefix:string -> out_channel -> unit =
      fun ?(prefix="") oc ->
        if CSet.is_empty !valid then
          wrn_msg "no log function registered (Log.print_opts)\n%!";
        CMap.iter (Printf.fprintf oc "%s%c: %s\n%!" prefix) !descr
end
