(** Keyword management. This module provides functions for declaring keywords,
    and for checking whether a given string is a keyword. It is mainly used to
    make sure that identifiers are not keywords. *)


(** List containing all the declared keywords. *)
let keywords : string list ref = ref []

(** [mem s] checks whether [s] has been declared as a keyword. *)
let mem : string -> bool = fun s ->
  List.mem s !keywords

(** [check s] checks whether [s] has been declared as a keyword, and if yes it
    calls [Decap.give_up ()] to cut the current parsing branch. *)
let check : string -> unit = fun s ->
  if mem s then Earley.give_up ()

(** [create kw] declares [kw] as a new keyword, and returns a parsing function
    for it. Note that it only accepts the keyword if it is not followed by any
    "keyword character" (letters, numbers, ...). The [Invalid_argument] excep-
    tion is raised when the given keyword has already been declared, or if the
    empty word [""] is given as input. *)
let create : string -> unit Earley.grammar = fun s ->
  if s = "" then invalid_arg "invalid keyword";
  if mem s  then invalid_arg "keyword already defined";
  keywords := s :: !keywords;
  let f str pos =
    let str = ref str in
    let pos = ref pos in
    for i = 0 to String.length s - 1 do
      let (c,str',pos') = Input.read !str !pos in
      if c <> s.[i] then Earley.give_up ();
      str := str'; pos := pos'
    done;
    let (c,_,_) = Input.read !str !pos in
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> Earley.give_up ()
    | _                                           -> ((), !str, !pos)
  in
  Earley.black_box f (Charset.singleton s.[0]) false s
