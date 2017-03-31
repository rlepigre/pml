(** Modified version of the [Hashbtl] library, to work with types containing
    functions. Physical equality is used when [Pervasives.compare] raises an
    exception. Note that this is only used when the hash function leads to a
    collision (and thus quite rarely). *)

(** The type of hash tables from type ['a] to type ['b]. *)
type ('a, 'b) t

(** [Hashtbl.create n] creates a new, empty hash table with initial size [n]
    ([n] should be on the order of the expected number of elements that will
    be in the table). The table is grown as needed so [n] is just an initial
    guess. *)
val create : int -> ('a, 'b) t

(** Empty a hash table. Use [reset] instead of [clear] to shrink the size of
    the bucket table to its initial size. *)
val clear : ('a, 'b) t -> unit

(** Empty a hash table and shrink the bucket table to its initial size. *)
val reset : ('a, 'b) t -> unit

(** Return a copy of the given hashtable. *)
val copy : ('a, 'b) t -> ('a, 'b) t

(** [Hashtbl.add tbl key v] adds a binding of [key] to [v] in table [tbl]. A
    previous bindings for [x] is not removed, but simply hidden. If any, the
    previous binding can be restored by calling [Hashtbl.remove tbl key]. *)
val add : ('a, 'b) t -> 'a -> 'b -> unit

(** [Hashtbl.find tbl key] returns the current binding of [key] in [tbl], or
    raises [Not_found] if no such binding exists. *)
val find : ('a, 'b) t -> 'a -> 'b

(** [Hashtbl.find_all tbl key] returns the list of all data associated  with
    [key] in [tbl]. The current binding is returned first, then the previous
    bindings, in reverse order of introduction in the table. *)
val find_all : ('a, 'b) t -> 'a -> 'b list

(** [Hashtbl.mem tbl key] checks if [key] is bound in [tbl]. *)
val mem : ('a, 'b) t -> 'a -> bool

(** [Hashtbl.remove tbl key] removes the current binding of [key] in  [tbl],
    restoring the previous binding if it exists. It does nothing if [key] is
    not bound in [tbl]. *)
val remove : ('a, 'b) t -> 'a -> unit

(** [Hashtbl.replace tbl key v] replaces the current binding of [key] by [v]
    in [tbl]. If [key] has no binding in [tbl], a binding of [key] to [v] is
    added to [tbl]. *)
val replace : ('a, 'b) t -> 'a -> 'b -> unit

(** [Hashtbl.iter f tbl] applies [f] to all bindings in table [tbl]. The key
    if given to [f] as its first argument, and the value as its second. Each
    Each binding is presented exactly once to [f].

    The order in which the bindings are passed to [f] is unspecified. If the
    table contains several bindings for the same key, they are passed to [f]
    in reverse order of introduction. In other words the most recent binding
    is passed first. *)
val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit

(** [Hashtbl.fold f tbl init] computes [(f kN dN ... (f k1 d1 init) ...)] in
    which [k1 ... kN] are the keys of all bindings in [tbl], and [d1 ... dN]
    are the associated values. Each binding is presented exactly once to the
    function [f].

    The order in which the bindings are passed to [f] is unspecified. If the
    table contains several bindings for the same key, they are passed to [f]
    in reverse order of introduction. In other words the most recent binding
    is passed first. *)
val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c

(** [Hashtbl.length tbl] returns the number of bindings in [tbl] in constant
    time. Multiple bindings are counted. *)
val length : ('a, 'b) t -> int
