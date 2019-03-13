include lib.stream
include lib.nat
include lib.int
include lib.int_proofs

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
    let d0 = dbl carry + (sbit_to_int x0 + sbit_to_int y0);
    if even d0 {
      {hd = sgn d0; tl = average_aux Zero x y}
    } else {
      let {hd = x1} = x {};
      let {hd = y1} = y {};
      let d1 = dbl d0 + (sbit_to_int x1 + sbit_to_int y1);
      let e : sbit = if ge d1 p2 { S } else { if le d1 n2 { P } else { Z } };
      let carry = d0 - (dbl (sbit_to_int e));
      {hd = e; tl = average_aux carry x y}
    }
  }

// Actual average function.
infix (⊕) = average priority 3 left associative
val average : real ⇒ real ⇒ real =
  average_aux Zero

type eq_stream⟨s1:τ,s2:τ⟩ = ∀n∈nat, nth n s1 ≡ nth n s2

val rec average_aux_idempotent : ∀x∈real, eq_stream⟨x, average_aux Zero x x⟩ =
  fun x n {
    let {hd; tl} = x {};
    set auto 2 2;
    case n {
      Zero → {}
      S[p] → use average_aux_idempotent tl p; {}
    }
  }


val average_idempotent : ∀x∈real, eq_stream⟨x, x ⊕ x⟩ =
  fun x { average_aux_idempotent x }

val rec average_aux_commutative :  ∀c∈int, ∀x y∈real,
                                    eq_stream⟨average_aux c x y, average_aux c y x⟩ =
  fun c x y n {
    let {hd=x0; tl=xs} = x {};
    let {hd=y0; tl=ys} = y {};
    let d0 = dbl c + (sbit_to_int x0 + sbit_to_int y0);
    use add_commutative (sbit_to_int x0) (sbit_to_int y0);
    if even d0 {
      eqns average_aux c x y {} ≡ { hd = sgn d0; tl = average_aux Zero xs ys };
      eqns average_aux c y x {} ≡ { hd = sgn d0; tl = average_aux Zero ys xs };
      case n {
        Zero → {}
        S[p] → average_aux_commutative Zero xs ys p
      }
    } else {
      set auto 0 2;
      let {hd = x1} = xs {};
      let {hd = y1} = ys {};
      let d1 = dbl d0 + (sbit_to_int x1 + sbit_to_int y1);
      let d2 = dbl d0 + (sbit_to_int y1 + sbit_to_int x1);
      eqns d1 ≡ d2 by add_commutative (sbit_to_int x1) (sbit_to_int y1);
      let e : sbit = if ge d1 p2 { S } else { if le d1 n2 { P } else { Z } };
      let c1 = d0 - (dbl (sbit_to_int e));
      eqns average_aux c x y {} ≡ { hd = e; tl = average_aux c1 xs ys };
      eqns average_aux c y x {} ≡ { hd = e; tl = average_aux c1 ys xs };
      case n {
        Zero → {}
        S[p] → average_aux_commutative c1 xs ys p
      }
    }
  }
