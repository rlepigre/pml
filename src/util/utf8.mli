(** A minimal modul for UTF8 encoding support. *)

(** [next str pos] returns the starting position of the next UTF8 character
    start from the (assumed valid) position [pos] in [str]. *)
val next : string -> int -> int

(** [len str] returns the UTF8 length of the given [string]. *)
val len : string -> int

(** [sub str start len] is the UTF8 equivalent of [String.sub]. *)
val sub : string -> int -> int -> string
