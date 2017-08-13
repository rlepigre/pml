// Type of streams.
type corec stream<a> = {} ⇒ {hd : a; tl : stream}

// Head of a stream.
val head : ∀a, stream<a> ⇒ a =
  fun s → (s {}).hd

// Tail of a stream.
val tail : ∀a, stream<a> ⇒ stream<a> =
  fun s → (s {}).tl

// Identity function.
val rec id : ∀a, stream<a> ⇒ stream<a> = fun s _ →
  let c = s {} in
  {hd = c.hd ; tl = id c.tl}

// Map function.
val rec map : ∀a b, (a ⇒ b) ⇒ stream<a> ⇒ stream<b> = fun f s _ →
  let c = s {} in
  {hd = f c.hd ; tl = map f c.tl}

include lib.nat
include lib.list

// Compute the list of the first n elements of a stream.
val rec take : ∀a, nat ⇒ stream<a> ⇒ list<a> = fun n s →
  case n {
    | Z    → Nil
    | S[k] → let c = s {} in
             let tl = take k c.tl in
             Cons[{hd = c.hd; tl = tl}]
  }

// Stream of zeroes.
val rec zeroes : stream<nat> = fun _ →
  {hd = Z; tl = zeroes}

// Stream of the natural numbers starting at n.
val rec naturals_from : nat ⇒ stream<nat> = fun n _ →
  {hd = n; tl = naturals_from S[n]}

// Stream of the natural numbers.
val naturals : stream<nat> = naturals_from Z
