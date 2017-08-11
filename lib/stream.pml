// Type of streams.
type corec stream<a> = {} ⇒ {hd : a; tl : stream}

// Identity function.
//val rec id : ∀a, stream<a> ⇒ stream<a> = fun s _ →
//  let c = s {} in
//  {hd = c.hd ; tl = id c.tl}

// Map function.
//val rec map : ∀a b, (a ⇒ b) ⇒ stream<a> ⇒ stream<b> = fun f s _ →
//  {hd = f (s {}).hd ; tl = map f (s {}).tl}
