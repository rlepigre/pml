type key = string

type 'a t

val empty : 'a t

val add : string -> 'a -> 'a t -> 'a t

val mem : string -> 'a t -> bool

val singleton : string -> 'a -> 'a t

val find : string -> 'a t -> 'a

val map : ('a -> 'b) -> 'a t -> 'b t

val mapi : (string -> 'a -> 'b) -> 'a t -> 'b t

val bindings : 'a t -> (string * 'a) list

val fold : (string -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val iter : (string -> 'a -> unit) -> 'a t -> unit

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val lift_box : 'a Bindlib.bindbox t -> 'a t Bindlib.bindbox

val map_box : ('b -> 'a Bindlib.bindbox) -> 'b t -> 'a t Bindlib.bindbox
