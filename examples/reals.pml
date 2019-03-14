include lib.stream
include lib.nat

val add_nat : nat ⇒ nat ⇒ nat = add

include lib.int
include lib.int_proofs

// Signed binary digit, element of {-1, 0, 1}.
type sbit = [P; Z; S]

// Opposite operation on binary digits.
val opp_sbit : sbit ⇒ sbit =
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
type mantisse = stream⟨sbit⟩

// Mantisse with size.
type smantisse⟨s⟩ = stream^s⟨sbit⟩

// Type of real numbers
type real = { man : mantisse; exp : int }

// Unique representation of -1 and 1.
val neg1 : mantisse = repeat P
val pos1 : mantisse = repeat S

// To compute the opposite, we juste take the opposite of every digit.
val opp_man : mantisse ⇒ mantisse =
  map opp_sbit

val opp : real ⇒ real = fun x {
  { man = opp_man x.man; exp = x.exp }
}

// Average of a single sbit and a mantisse.
val sbit_average : sbit ⇒ mantisse ⇒ mantisse =
  fun d r { cons d r }

// Average function with a carry.
val rec average_aux : ∀s, int ⇒ smantisse⟨s+ₒ1⟩ ⇒ smantisse⟨s+ₒ1⟩ ⇒ smantisse⟨s⟩ =
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

// Actual average function, keeping size information (for multiplication).
infix (⊕) = average priority 3 left associative
val average : ∀s, smantisse⟨s+ₒ1⟩ ⇒ smantisse⟨s+ₒ1⟩ ⇒ smantisse⟨s⟩ =
  average_aux Zero

// check that with subtyping type is general enough
val test : mantisse ⇒ mantisse ⇒ mantisse = average

// equality on streams: probably equivalent to ≡ and stronger than
// equality on reals
type eq_stream⟨s1:τ,s2:τ⟩ = ∀n∈nat, nth n s1 ≡ nth n s2

val rec average_aux_idempotent : ∀x∈mantisse, eq_stream⟨x, average_aux Zero x x⟩ =
  fun x n {
    let {hd; tl} = x {};
    set auto 2 2;
    case n {
      Zero → {}
      S[p] → use average_aux_idempotent tl p; {}
    }
  }

val average_idempotent : ∀x∈mantisse, eq_stream⟨x, x ⊕ x⟩ =
  fun x { average_aux_idempotent x }

val rec average_aux_commutative :  ∀c∈int, ∀x y∈mantisse,
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

val rec average_commutative :  ∀x y∈mantisse,
                                    eq_stream⟨x ⊕ y, y ⊕ x⟩ =
  fun x y { average_aux_commutative Zero x y }

// From average we get addition using a few extra function

// shift n x is x / 2^n
val rec shift : nat ⇒ mantisse ⇒ mantisse = fun n x {
  case n {
    Zero → x
    S[p] → fun _ { { hd = Z; tl = shift p x } }
  }
}

// tell which argument is the maximum and the absolute value of
// the difference
val rec int_cmp : int ⇒ int ⇒ [ Left of nat; Right of nat ] =
  fun n m {
    case n {
      Zero →
        case m {
          Zero → Left[Zero]
          S[m] → Right[S[m]]
          P[m] → Left[S[opp_neg m]]
        }
      S[n] →
        case m {
          Zero → Left[S[n]]
          S[m] → int_cmp n m
          P[m] → Left[S[S[add_nat n (opp_neg m)]]]
        }
      P[n] →
        case m {
          Zero → Right[S[opp_neg n]]
          S[m] → Right[S[S[add_nat (opp_neg n) m]]]
          P[m] → int_cmp n m
        }
    }
  }

val add_int : int ⇒ int ⇒ int = add

// addition (no normalisation is performed, the mantissa
// will often start with zeros. Could try to remove a fixed
// number of zeros to give smaller exponent
// remark :  (S P = Z S) so we can remove more then zeros ⋯
// remark : removing all zeros is non terminating !
val rec add : real ⇒ real ⇒ real = fun x y {
  case int_cmp x.exp y.exp {
    Left[n]  → { man = average x.man (shift n y.man)
               ; exp = suc x.exp }
    Right[n] → { man = average (shift n x.man) y.man
               ; exp = suc y.exp }
  }
}

val rec minus : real ⇒ real ⇒ real = fun x y {
  x + opp y
}

// code for multiplication of mantissa
val mul_sbit : sbit ⇒ sbit ⇒ sbit = fun a b {
  case a {
    Z → Z
    S → b
    P → opp_sbit b
  }
}

val rec mul_sbit_mantisse : ∀s, sbit ⇒ smantisse⟨s⟩ ⇒ smantisse⟨s⟩ = fun b x _ {
  let { hd = x0; tl = x } = x {};
  { hd = mul_sbit b x0; tl = mul_sbit_mantisse b x }
}

val rec mul_man : mantisse ⇒ mantisse ⇒ mantisse = fun x y {
  let s such that _ : smantisse⟨s⟩;
  fun  _ {
    let { hd = x0; tl = x } = x {};
    let { hd = y0; tl = y } = y {};
    let { hd = y1; tl = y } = y {};
    // FIXME: using infix notation gives a strange ortage error
    let p : smantisse⟨s+ₒ1⟩ = average (mul_sbit_mantisse y0 x)
                            (average (mul_sbit_mantisse x0 y) (mul_sbit_mantisse y1 x));
    let q : smantisse⟨s+ₒ1⟩ =
      fun (_ :{}){ { hd = mul_sbit x0 y0
                   ; tl = fun (_:{}) { { hd = mul_sbit x0 y1
                                       ; tl = mul_man x y } } } };
    let r = average p q; // FIXME: applying directly unit fails
     r {}
  }
}

// multiplication of reals
val mul : real ⇒ real ⇒ real = fun x y {
  { man = mul_man x.man y.man; exp = add_int x.exp y.exp }
}