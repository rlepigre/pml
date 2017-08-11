type ('a, 'b) t =
  | Eq  : ('a, 'a) t
  | NEq : ('a, 'b) t

type ('a, 'b) eq = ('a, 'b) t

let (===) : type a b. a -> b -> (a, b) eq =
  fun x y -> if Obj.repr x == Obj.repr y then Obj.magic Eq else NEq

let (&&&) : type a b c d. (a, b) eq -> (c, d) eq -> (a -> c, b -> d) eq =
  fun x y -> match (x, y) with (Eq, Eq) -> Eq | _ -> NEq
