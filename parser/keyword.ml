let keywords = Hashtbl.create 20

(** Tests whether the given string is a keyword. *)
let mem : string -> bool = Hashtbl.mem keywords

(** Check if the given [string] is a keyword and calls [Decap.give_up ()] when
    this is the case. *)
let check : string -> unit = fun s ->
  if mem s then Earley.give_up ()

(** Create a new keyword. The exception [Invalid_argument] is raised when  the
    fiven keyword has already been declared, or if it is empty ([""]). *)
let create : string -> unit Earley.grammar = fun s ->
  if s = "" then invalid_arg "invalid keyword";
  if mem s  then invalid_arg "keyword already defined";
  Hashtbl.add keywords s s;
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
