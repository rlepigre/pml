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

// Stream of the natural numbers.
val rec nat_aux : (nat ⇒ stream<nat>) = fun i _ →
    {hd = i; tl = nat_aux S[i]}

val naturals : stream<nat> = nat_aux Z

// Stream of the natural numbers.
//val naturals : stream<nat> =
//  let nat_aux : (nat ⇒ stream<nat>) = fix (fun f i _ →
//                       {hd = i; tl = nat_aux S[i]})
//  in nat_aux Z
// FIXME loops


// Stream of the natural numbers.
//val rec naturals : stream<nat> = fun _ →
//  {hd = Z; tl = map (fun n → S[n]) naturals}
// FIXME needs size preserving map function
