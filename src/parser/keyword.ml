(** Keyword management. This module provides functions for declaring keywords,
    and for checking whether a given string is a keyword. It is mainly used to
    make sure that identifiers are not keywords. *)

open Pacomb

(** List containing all the declared keywords. *)
let keywords : string list ref = ref []

(** [mem s] checks whether [s] has been declared as a keyword. *)
let mem : string -> bool = fun s ->
  List.mem s !keywords

(** [check s] checks whether [s] has been declared as a keyword, and if yes it
    calls [Decap.give_up ()] to cut the current parsing branch. *)
let check : string -> unit = fun s ->
  if mem s then Lex.give_up ()

(** [create kw] declares [kw] as a new keyword, and returns a parsing function
    for it. Note that it only accepts the keyword if it is not followed by any
    "keyword character" (letters, numbers, ...). The [Invalid_argument] excep-
    tion is raised when the given keyword has already been declared, or if the
    empty word [""] is given as input. *)
let create : string -> unit Grammar.t = fun s ->
  if s = "" then invalid_arg "invalid keyword";
  if mem s  then invalid_arg "keyword already defined";
  keywords := s :: !keywords;
  let test = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true
    | _                                           -> false
  in Grammar.term (Lex.keyword s test ())
