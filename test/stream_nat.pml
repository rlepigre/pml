include lib.stream

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
