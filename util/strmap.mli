include Map.S with type key = string

val lift_box : 'a Bindlib.bindbox t -> 'a t Bindlib.bindbox

val map_box : ('b -> 'a Bindlib.bindbox) -> 'b t -> 'a t Bindlib.bindbox
