type key = string

type 'a t

val empty : 'a t

val length : 'a t -> int

val is_empty : 'a t -> bool

val add : string -> 'a -> 'a t -> 'a t

val mem : string -> 'a t -> bool

val singleton : string -> 'a -> 'a t

val find : string -> 'a t -> 'a

val map : ('a -> 'b) -> 'a t -> 'b t

val mapi : (string -> 'a -> 'b) -> 'a t -> 'b t

val bindings : 'a t -> (string * 'a) list

val sort : ('a -> 'a -> int) -> 'a t -> 'a t

val fold : (string -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val fold2 : ('b -> 'a -> 'a -> 'b) -> 'b -> 'a t -> 'a t -> 'b

val fold_map : (string -> 'a -> 'b -> 'c * 'b) -> 'a t -> 'b -> 'c t * 'b

val iter : (string -> 'a -> unit) -> 'a t -> unit

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

val for_all : (string -> 'a -> bool) -> 'a t -> bool

val exists : (string -> 'a -> bool) -> 'a t -> bool

val lift_box : 'a Bindlib.box t -> 'a t Bindlib.box

val map_box : ('b -> 'a Bindlib.box) -> 'b t -> 'a t Bindlib.box

val hash : ('a -> int) -> 'a t -> int
