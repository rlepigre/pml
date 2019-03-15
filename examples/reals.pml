include lib.stream
include lib.nat

def add_nat = add

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
// used as mantissa to represent reals
type man = stream⟨sbit⟩

// Mantisse with size.
type sman⟨s⟩ = stream^s⟨sbit⟩

// Unique representation of -1 and 1.
val neg1 : man = repeat P
val pos1 : man = repeat S

// To compute the opposite, we juste take the opposite of every digit.
val opp_man : man ⇒ man =
  map opp_sbit

// Average of a single sbit and a man.
val sbit_average : sbit ⇒ man ⇒ man =
  fun d r { cons d r }

// Average function with a carry.
val rec average_aux : ∀s, int ⇒ sman⟨s+ₒ1⟩ ⇒ sman⟨s+ₒ1⟩ ⇒ sman⟨s⟩ =
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
val average : ∀s, sman⟨s+ₒ1⟩ ⇒ sman⟨s+ₒ1⟩ ⇒ sman⟨s⟩ =
  average_aux Zero

// check that with subtyping type is general enough
val test : man ⇒ man ⇒ man = average

// equality on streams: probably equivalent to ≡ and stronger than
// equality on reals, but ok for commutativity
type eq_stream⟨s1:τ,s2:τ⟩ = ∀n∈nat, nth n s1 ≡ nth n s2

val rec average_aux_idempotent : ∀x∈man, eq_stream⟨x, average_aux Zero x x⟩ =
  fun x n {
    let {hd; tl} = x {};
    set auto 2 2;
    case n {
      Zero → {}
      S[p] → use average_aux_idempotent tl p; {}
    }
  }

val average_idempotent : ∀x∈man, eq_stream⟨x, x ⊕ x⟩ =
  fun x { average_aux_idempotent x }

val rec average_aux_commutative :  ∀c∈int, ∀x y∈man,
       eq_stream⟨average_aux c x y, average_aux c y x⟩ =
  fun c x y n {
    let {hd=x0; tl=xs} = x {};
    let {hd=y0; tl=ys} = y {};
    let d0 = dbl c + (sbit_to_int x0 + sbit_to_int y0);
    use add_commutative (sbit_to_int x0) (sbit_to_int y0);
    if even d0 {
      eqns average_aux c x y {} ≡ { hd = sgn d0; tl = average_aux p0 xs ys };
      eqns average_aux c y x {} ≡ { hd = sgn d0; tl = average_aux p0 ys xs };
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

val rec average_commutative :  ∀x y∈man,
                                    eq_stream⟨x ⊕ y, y ⊕ x⟩ =
  fun x y { average_aux_commutative Zero x y }


// code for multiplication of mantissa
val mul_sbit : sbit ⇒ sbit ⇒ sbit = fun a b {
  case a {
    Z → Z
    S → b
    P → opp_sbit b
  }
}

val rec mul_sbit_man : ∀s, sbit ⇒ sman⟨s⟩ ⇒ sman⟨s⟩ = fun b x _ {
  let { hd = x0; tl = x } = x {};
  { hd = mul_sbit b x0; tl = mul_sbit_man b x }
}

val rec mul_man : man ⇒ man ⇒ man = fun x y {
  let s such that _ : sman⟨s⟩;
  fun  _ {
    let { hd = x0; tl = x } = x {};
    let { hd = y0; tl = y } = y {};
    let { hd = y1; tl = y } = y {};
    let p : sman⟨s+ₒ1⟩ =
      mul_sbit_man y0 x ⊕ (mul_sbit_man x0 y ⊕ mul_sbit_man y1 x);
    let q : sman⟨s+ₒ1⟩ =
      fun (_ :{}){ { hd = mul_sbit x0 y0
                   ; tl = fun (_:{}) { { hd = mul_sbit x0 y1
                                       ; tl = mul_man x y } } } };
    (p ⊕ q) {}
  }
}

// From mantissa, i.e. [-1,1] we get real
// Type of real numbers
type real = { man : man; exp : nat }

type eq_real⟨x:τ,y:τ⟩ = eq_stream⟨x.man,y.man⟩ × x.exp ≡ y.exp

val opp : real ⇒ real = fun x {
  { man = opp_man x.man; exp = x.exp }
}

// From average we get addition using a few extra function

// shift n x is x / 2^n
val rec shift : nat ⇒ man ⇒ man = fun n x {
  case n {
    Zero → x
    S[p] → fun _ { { hd = Z; tl = shift p x } }
  }
}

// tell which argument is the maximum and the absolute value of
// the difference
val rec nat_cmp : ∀n m ∈ nat, [ Eq of n ≡ m; Left of nat; Right of nat ] =
  fun n m {
    case n {
      Zero →
        case m {
          Zero → Eq
          S[m] → Right[S[m]]
        }
      S[n] →
        case m {
          Zero → Left[S[n]]
          S[m] → nat_cmp n m
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
  case nat_cmp x.exp y.exp {
    Eq       → { man = average x.man y.man
               ; exp = S[x.exp] }
    Left[n]  → { man = average x.man (shift n y.man)
               ; exp = S[x.exp] }
    Right[n] → { man = average (shift n x.man) y.man
               ; exp = S[y.exp] }
  }
}

val opp_cmp : [ Eq; Left of nat; Right of nat ] ⇒ [ Eq; Left of nat; Right of nat ] =
  fun a {
    case a {
      Eq       → Eq
      Left[x]  → Right[x]
      Right[x] → Left[x]
    }
  }

val rec nat_cmp_comm : ∀n m∈nat, nat_cmp m n ≡ opp_cmp(nat_cmp n m) =
  fun n m {
    case n {
      Zero →
        case m {
          Zero → {}
          S[_] → {}
        }
      S[n] →
        case m {
          Zero → {}
          S[m] → nat_cmp_comm n m
        }
    }
  }

val rec add_commutative : ∀x y∈real, eq_real⟨add x y, add y x⟩ =
  fun x y {
    use nat_cmp_comm x.exp y.exp;
    case nat_cmp x.exp y.exp {
      Eq       → let p = average_commutative x.man y.man;
                 (p, {})
      Left[n]  → let p = average_commutative x.man (shift n y.man);
                 (p, {})
      Right[n] → let p = average_commutative (shift n x.man) y.man;
                 (p, {})
    }
  }

val rec minus : real ⇒ real ⇒ real = fun x y {
  x + opp y
}

include lib.nat_proofs

// multiplication of reals
val mul : real ⇒ real ⇒ real = fun x y {
  { man = mul_man x.man y.man; exp = add_nat x.exp y.exp }
}
