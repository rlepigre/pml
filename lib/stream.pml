// Type of streams.
type corec stream<a> = {} ⇒ {hd : a; tl : stream}

// Identity function.
val rec id : ∀a, stream<a> ⇒ stream<a> = fun s _ →
  let c = s {} in
  {hd = c.hd ; tl = id c.tl}

// Map function.
val rec map : ∀a b, (a ⇒ b) ⇒ stream<a> ⇒ stream<b> = fun f s _ →
  let c = s {} in
  {hd = f c.hd ; tl = map f c.tl}

include lib.nat

// Stream of zeroes.
val rec zeroes : stream<nat> = fun _ →
  {hd = Z; tl = zeroes}

// Stream of the natural numbers starting at n.
val rec naturals_from : nat ⇒ stream<nat> = fun n _ →
  {hd = n; tl = nat_aux S[n]}

// Stream of the natural numbers.
val naturals : stream<nat> = nat_aux Z
