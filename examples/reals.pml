include lib.stream
include lib.bool
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

def bti = sbit_to_int

// Representation of a real number in the interval [-1,1].
// The stream of binary digits d₁∷d₂∷... corresponds to the sum Σₖ (dₖ / 2ᵏ).
// used as mantissa to represent reals
type man = stream⟨sbit⟩

// Mantisse with size.
type sman⟨s⟩ = stream^s⟨sbit⟩

// Unique representation of -1 and 1.
val mann1 : man = repeat P
val man1 : man = repeat S
val man0 : man = repeat Z

// To compute the opposite, we juste take the opposite of every digit.
val opp_man : man ⇒ man =
  map opp_sbit

//bounded digit stream
type bint⟨n⟩ = { x ∈ int | le x n && ge x (opp n)}

type bds⟨n:τ⟩ = stream⟨bint⟨n⟩⟩

type sbds⟨s:κ,n:τ⟩ = stream^s⟨bint⟨n⟩⟩

val rec divideBy : ∀o:κ, ∀n∈nat, ∀s∈sbds⟨o+ₒ2,n⟩, sman⟨o⟩ =
  fun n x _ {
    let { hd = a; tl = x } = x {};
    let { hd = b; tl = x } = x {};
    let d = p2 * a + b;
    show le a n using (set auto 1 2; {});
    deduce ge a (opp n);
    show le b n using (set auto 1 2; {});
    deduce ge b (opp n);
    show le (p2 * a) (p2 * n) using add_increasing a n a n {} {};
    show le d (p3 * n) using add_increasing (p2 * a) (p2 * n) b n {} {};
    show ge (p2 * a) (p2 * (opp n))
      using add_increasing (opp n) a (opp n) a {} {};
    show ge d (p3 * (opp n))
      using add_increasing (p2 * (opp n)) (p2 * a) (opp n) b {} {};
    if le d (opp n) {
      let k : int = d + p2 * n;
      let _ : le k n = (
        show le k (opp n + p2 * n)
          using add_increasing_left d (opp n) (p2 * n) {};
        eqns (opp n) + p2 * n
          ≡ (opp n + n) + n by add_associative (opp n) n n
          ≡ n by (add_inv n; add_commutative (opp n) n);
        {}
        );
      let _ : ge k (opp n) = (
        show ge k (p3 * opp n + p2 * n)
          using add_increasing_left (p3 * opp n) d (p2 * n) {};
        eqns p3 * opp n + p2 * n // better proof are possible ;-)
          ≡ (p3 * opp n + n) + n by add_associative (p3 * opp n) n n
          ≡ (p2 * opp n + (opp n + n)) + n
               by add_associative (p2 * opp n) (opp n) n
          ≡ (p2 * opp n + n) by (add_inv n;
                                  add_commutative (opp n) n;
                                  add_zero_right (p2 * opp n))
          ≡ opp n + (opp n + n)
               by add_associative (opp n) (opp n) n
          ≡ opp n
               by (add_inv n;
                   add_commutative (opp n) n;
                   add_zero_right (opp n));
        {}
        );
      { hd = P; tl = divideBy n (fun _ { { hd = k; tl = x } }) }
    } else { if ge d n {
      let k : int = d - p2 * n;
      let _ : le k n = (
        show le k (p3 * n - p2 * n)
          using (add_increasing_left d (p3 * n) (opp (p2 * n)) {};
                 add_opp d (p2 * n);
                 add_opp (p3 * n) (p2 * n));
        eqns p3 * n - p2 * n // better proof are possible ;-)
          ≡ p3 * n + opp (n + n)  by add_opp (p3 * n) (p2 * n)
          ≡ p3 * n + (opp n + opp n) by add_opp_opp n n
          ≡ (p3 * n + opp n) + opp n
              by add_associative (p3 * n) (opp n) (opp n)
          ≡ (p2 * n + (n + opp n)) + opp n
              by add_associative (p2 * n) n (opp n)
          ≡ (p2 * n + opp n) by (add_inv n;
                                  add_zero_right (p2 * n))
          ≡ n + (n + opp n) by add_associative n n (opp n)
          ≡ n by (add_inv n; add_zero_right n);
          {});
      let _ : ge k (opp n) =  (
        show ge k (n - p2 * n)
          using (add_increasing_left n d (opp (p2 * n)) {};
                  add_opp n (p2 * n);
                  add_opp d (p2 * n));
        eqns n - p2 * n
          ≡ n + (opp n + opp n) by (add_opp n (p2 * n) ; add_opp_opp n n)
          ≡ (n + opp n) + opp n by add_associative n (opp n) (opp n)
          ≡ opp n by add_inv n;
        {}
        );
      { hd = S; tl = divideBy n (fun _ { { hd = k; tl = x } }) }
    } else {
      let _ : le d n = (
        deduce ge d n ≡ false;
        show lt d n using not_ge_is_lt d n {};
        show le d n using lt_is_le d n {};
        {});
      let _ : ge d (opp n) = (
        deduce le d (opp n) ≡ false;
        show gt d (opp n) using not_le_is_gt d (opp n) {};
        show ge d (opp n) using gt_is_ge d (opp n) {};
        {}
      );
      { hd = Z; tl = divideBy n (fun _ { { hd = d; tl = x } }) }
    }}
  }

val rec average_aux : ∀s, sman⟨s⟩ ⇒ sman⟨s⟩ ⇒ sbds⟨s,p2⟩ =
  fun x y _ {
    let {hd = x0; tl = x} = x {};
    let {hd = y0; tl = y} = y {};
    let d = bti x0 + bti y0;
    let _ : le d p2 = (set auto 2 1; {});
    let _ : ge d n2 = (set auto 2 1; {});
    { hd = d; tl = average_aux x y }
  }


// Actual average function, keeping size information (for multiplication).
infix (⊕) = average priority 3 left associative
val average : ∀s, sman⟨s+ₒ2⟩ ⇒ sman⟨s+ₒ2⟩ ⇒ sman⟨s⟩ = fun x y {
  divideBy p2 (average_aux x y)
}

// check that with subtyping type is general enough
val test : man ⇒ man ⇒ man = average

val rec big_average_aux : stream⟨man⟩ ⇒ bds⟨p4⟩ = fun xs _ {
   let { hd = x0; tl = xs } = xs {};
   let { hd = x1; tl = xs } = xs {};
   let { hd = a ; tl = x0 } = x0 {};
   let { hd = b ; tl = x0 } = x0 {};
   let { hd = c ; tl = x1 } = x1 {};
   let d = p2* bti a + bti b + bti c;
   let _ : le d p4 = (set auto 3 1; {});
   let _ : ge d n4 = (set auto 3 1; {});
   { hd = d
   ; tl = big_average_aux (fun _ { { hd = average x0 x1; tl = xs } }) }
}

val big_average : stream⟨man⟩ ⇒ man = fun xs {
  divideBy p4 (big_average_aux xs)
}

val rec affine_aux : man ⇒ man ⇒ man ⇒ man ⇒ stream⟨man⟩ = fun x xy y z _ {
  let { hd = z0; tl = z } = z {};
  let d = case z0 {
    P → x
    Z → xy
    S → y
  };
  { hd = d; tl = affine_aux x xy y z }
}

val affine : man ⇒ man ⇒ man ⇒ man = fun x y z {
  let xy = average x y;
  big_average (affine_aux x xy y z)
}

val mul_man : man ⇒ man ⇒ man = fun x y { affine (opp_man x) x y }


// From mantissa, i.e. [-1,1] we get real
// Type of real numbers
type real = { man : man; exp : nat }

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

// addition (no normalisation is performed, see below)
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

type cmp = [ Eq; Left of nat; Right of nat ]
val opp_cmp : cmp ⇒ cmp =
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

val rec minus : real ⇒ real ⇒ real = fun x y {
  x + opp y
}

// multiplication of reals
val mul : real ⇒ real ⇒ real = fun x y {
  { man = mul_man x.man y.man; exp = add_nat x.exp y.exp }
}

// non zero exponent only for mantissa starting with "10" "11" or "-10"
// "-1-1"
val rec norm_aux : nat ⇒ man ⇒ real = fun n x {
  case n {
    Zero → { exp = n; man = x }
    S[p] → let {hd = x0; tl = x'} = x {};
           case x0 {
             Z → norm_aux p x
             S → let { hd = x1; tl = x'} = x' {};
                 case x1 {
                   Z → { exp = n; man = x }
                   S → { exp = n; man = x }
                   P → norm_aux p (fun _ { {hd = S; tl = x'} })
                 }
             P → let { hd = x1; tl = x'} = x' {};
                 case x1 {
                   Z → { exp = n; man = x }
                   P → { exp = n; man = x }
                   S → norm_aux p (fun _ { {hd = P; tl = x'} })
                 }
           }
  }
}

val rec norm : real ⇒ real = fun x { norm_aux x.exp x.man }

// same kind of function allows to define non zero
val rec sign_approx : nat ⇒ man ⇒ sbit = fun n x {
  case n {
    Zero → Z
    S[p] → let {hd = x0; tl = x'} = x {};
           case x0 {
             Z → sign_approx p x'
             S → let { hd = x1; tl = x'} = x' {};
                 case x1 {
                   Z → S
                   S → S
                   P → sign_approx p (fun _ { {hd = S; tl = x'} })
                 }
             P → let { hd = x1; tl = x'} = x' {};
                 case x1 {
                   Z → P
                   P → P
                   S → sign_approx p (fun _ { {hd = P; tl = x'} })
                 }
           }
  }
}

//type for sign of real numbers
type neg⟨a⟩ = a → ∀x,x
type non_zero⟨x:τ⟩ = ∃n∈nat, sign_approx n x.man ≠ Z
type is_zero⟨x:τ⟩ = ∀n∈nat, sign_approx n x.man ≡ Z
type cis_zero⟨x:τ⟩ = ∀n∈nat, neg⟨sign_approx n x.man ≠ Z⟩
type positive⟨x:τ⟩ = ∃n∈nat, sign_approx n x.man ≡ S
type negative⟨x:τ⟩ = ∃n∈nat, sign_approx n x.man ≡ P
type diff_reals⟨x:τ,y:τ⟩ = non_zero⟨x - y⟩
type eq_reals⟨x:τ,y:τ⟩ = is_zero⟨x - y⟩

// i2 x = 1 / (2 - x)
val rec power_stream_aux : man ⇒ man ⇒ stream⟨man⟩ = fun x y _ {
  { hd = y; tl = power_stream_aux x (mul_man x y) }
}
val power_stream : man ⇒ stream⟨man⟩ = fun x { power_stream_aux x man1 }
val i2 : man ⇒ man = fun x { big_average (power_stream x) }

val rec inv_aux : ∀n m∈nat, ∀x, x ∈ man | sign_approx n x ≠ Z ⇒ real
  = fun n m x {
    // invariant X = 2^{-m} x
    case n {
      Zero → ✂
      S[p] →
        let {hd = x0; tl = x'} = x {};
        case x0 {
          Z → inv_aux p S[m] x'
          S → let { hd = x1; tl = x'} = x' {};
              case x1 {
                Z → // X = 2^(-m-2) + 2 + x1
                    //   = 2^(-m-2) + 2 - (-x1)
                    { exp = S[S[m]]; man = i2 (opp_man x') }
                S → // X = 2^(-m-1) + 1 + 1/2 + x1
                    //   = 2^(-m-1) + 2 - (1/2 - x1)
                    { exp = S[m]
                    ; man = i2 (fun _ { { hd = S; tl = opp_man x' } })}
                P → inv_aux p S[m] (fun _ { {hd = S; tl = x'} })
              }
          P → let { hd = x1; tl = x'} = x' {};
              case x1 {
                Z → // X = 2^(-m-2) - (2 - x1)
                    { exp = S[S[m]]; man = opp_man (i2 x') }
                P → // X = 2^(-m-1) - 1 - 1/2 + x1
                    //   = 2^(-m-1) - (2 - (-1/2 + x1))
                    { exp = S[m]
                    ; man = opp_man (i2 (fun _ { { hd = P; tl = x' } }))}
                S → inv_aux p S[m] (fun _ { {hd = P; tl = x'} })
              }
        }
    }
  }

val inv : ∀x∈ real, non_zero⟨x⟩ ⇒ real
  = fun x h {
    let y = inv_aux h.1 Zero x.man;
    case nat_cmp y.exp x.exp {
      Left[e]  → { exp = e; man = y.man }
      Right[e] → { exp = 0; man = shift e y.man }
      Eq       → { exp = 0; man = y.man }
    }
  }

include lib.either

val zero_or_inv
      : ∀x, x∈real ⇒
          either⟨cis_zero⟨x⟩, ∃h∈non_zero⟨x⟩, { y ∈ real | y ≡ inv x h}⟩
= fun x {
  save a {
    InL[fun n h { restore a (let nz = (n,h); InR[(nz, inv x nz)])}]
  }
}

val rec print_man : nat ⇒ man →_(p) {} = fun n x {
  case n {
    Zero → {}
    S[p] → let { hd = x0; tl = x } = x {};
           case x0 {
             S → print "1"; print_man p x
             Z → print "0"; print_man p x
             P → print "(-1)"; print_man p x
           }
  }
}

val rec print_bds : nat ⇒ ∀k, bds⟨k⟩ →_(p) {} = fun n x {
  case n {
    Zero → {}
    S[p] → let { hd = x0; tl = x } = x {};
           print_int x0; print " "; print_bds p x
  }
}

val print_real : nat ⇒ real →_(p) {} = fun n x {
  print "0."; print_man n x.man; print "E"; print_nat x.exp
}
