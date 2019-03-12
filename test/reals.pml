include lib.stream
include lib.int

// Signed binary digit, element of {-1, 0, 1}.
type sbit = [P; Z; S]

// Opposite operation on binary digits.
val op_sbit : sbit ⇒ sbit =
  fun d {
    case d {
      P → S
      Z → Z
      S → P
    }
  }

// Convert single digit to integer.
val sbit_to_int : sbit ⇒ int =
  fun d {
    case d {
      P → n1
      Z → p0
      S → p1
    }
  }

// Representation of a real number in the interval [-1,1].
// The stream of binary digits d₁∷d₂∷... corresponds to the sum Σₖ (dₖ / 2ᵏ).
type real = stream⟨sbit⟩

// Real with size.
type sreal⟨s⟩ = stream^s⟨sbit⟩

// Unique representation of -1 and 1.
val neg1 : real = repeat P
val pos1 : real = repeat S

// To compute the opposite, we juste take the opposite of every digit.
val opp : real ⇒ real =
  map op_sbit

// Average of a single sbit real and a real.
val sbit_average : sbit ⇒ real ⇒ real =
  fun d r { cons d r }

// Average function with a carry.
val rec average_aux : ∀s, int ⇒ sreal⟨s+1⟩ ⇒ sreal⟨s+1⟩ ⇒ sreal⟨s⟩ =
  fun carry x y _ {
    let {hd = x0; tl = x} = x {};
    let {hd = y0; tl = y} = y {};
    let d0 = add (dbl carry) (add (sbit_to_int x0) (sbit_to_int y0));
    if even d0 {
      {hd = sgn d0; tl = average_aux Z x y}
    } else {
      let {hd = x1} = x {};
      let {hd = y1} = y {};
      let d1 = add (dbl d0) (add (sbit_to_int x1) (sbit_to_int y1));
      let e : sbit = if ge d1 p2 { S } else { if le d1 n2 { P } else { Z } };
      let carry = sub d0 (dbl (sbit_to_int e));
      {hd = e; tl = average_aux carry x y}
    }
  }

// Actual average function.
infix (⊕) = average priority 3 left associative
val average : real ⇒ real ⇒ real =
  average_aux Z

type corec eq_stream⟨s1:τ,s2:τ⟩ =
  {} ⇒ { hd : s1.hd ≡ s2.hd; tl : eq_stream }

// should work, but must prove a property of average_aux ⋯
val rec average_aux_idempotent : ∀x∈real, eq_stream⟨x, average_aux Z x x⟩ =
  fun x _ {
    let {hd; tl} = x {};
    use average_aux_idempotent tl;
    case hd {
      P → {--}
      Z → {--}
      S → {--}
    }
  }

//val average_idempotent : ∀a, a ⊕ a ≡ a =
//  fun a {
//    {- TODO -}
//  }
