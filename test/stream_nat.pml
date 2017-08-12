include lib.stream

// Stream of the natural numbers.
val naturals : stream<nat> =
  let aux : (nat ⇒ stream<nat>) = ((fix (fun f i _ →
                       {hd = i; tl = f S[i]})) : (nat ⇒ stream<nat>))
  in aux Z

// Stream of the natural numbers.
//val rec naturals : stream<nat> = fun _ →
//  {hd = Z; tl = map (fun n → S[n]) naturals}
// FIXME needs size preserving map function
