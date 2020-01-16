// Type of streams.
type corec stream⟨a⟩ = lazy⟨{hd : a; tl : stream⟨a⟩}⟩

// Head of a stream.
val head : ∀a, stream⟨a⟩ ⇒ a =
  fun s { (force s).hd }

// Tail of a stream.
val tail : ∀a, ∀s, stream^(s+ₒ1)⟨a⟩ ⇒ stream^s⟨a⟩ =
  fun s { (force s).tl }

// Head and tail of a string together.
val get : ∀a, ∀s, stream^(s+ₒ1)⟨a⟩ ⇒ a × stream^s⟨a⟩ =
  fun s {
    let {hd; tl} = force s;
    (hd, tl)
  }

// Construction function.
val cons : ∀a, ∀s, a ⇒ stream^s⟨a⟩ ⇒ stream^(s+ₒ1)⟨a⟩ =
  fun hd tl { lazy { {hd; tl} } }

// Build a stream containing only the given element.
val rec repeat : ∀a, a ⇒ stream⟨a⟩ =
  fun hd { lazy { {hd; tl = repeat hd} } }

// Identity function.
val rec id : ∀a, ∀s, stream^s⟨a⟩ ⇒ stream^s⟨a⟩ =
  fun s { lazy {
    let c = force s;
    {hd = c.hd ; tl = id c.tl}
  } }

// Map function.
val rec map : ∀a b, ∀s, (a ⇒ b) ⇒ stream^s⟨a⟩ ⇒ stream^s⟨b⟩ =
  fun f s { lazy {
    let {hd ; tl} = force s;
    {hd = f hd ; tl = map f tl}
  } }

include lib.nat
include lib.list

// Compute the list of the first n elements of a stream.
val rec nth : ∀a, nat ⇒ stream⟨a⟩ ⇒ a =
  fun n s {
    case n {
           | Zero → (force s).hd
           | S[k] → nth k (force s).tl
    }
  }

// Compute the list of the first n elements of a stream.
val rec takes : ∀a, nat ⇒ stream⟨a⟩ ⇒ list⟨a⟩ =
  fun n s {
    case n {
           | Zero → Nil
           | S[k] → let c = force s;
                    let tl = takes k c.tl;
                    Cons[{hd = c.hd; tl = tl}]
    }
  }

// Stream of zeroes.
val rec zeroes : stream⟨nat⟩ =
  lazy { {hd = Zero; tl = zeroes} }

// Stream of the natural numbers starting at n.
val rec naturals_from : nat ⇒ stream⟨nat⟩ =
  fun n { lazy { {hd = n; tl = naturals_from S[n]} } }

// Stream of the natural numbers.
val naturals : stream⟨nat⟩ = naturals_from Zero
