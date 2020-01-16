// Unary natural numbers.

// The type of unary natural numbers.
type rec nat = [Zero ; S of nat]

// Smart constructors for zero and the successor.
val zero : nat = Zero
val succ : nat ⇒ nat = fun n { S[n] }

// With dble can use natural numbers!
val rec dble : nat ⇒ nat = fun n { case n { 0 → 0 | S[p] → S[S[dble p]] }}

// Usual numbers.
val one : nat = 1
val two : nat = 2

//// Usual operations ////////////////////////////////////////////////////////

// Predecessor function for non-zero numbers.
val pred : [S of nat] ⇒ nat = fun n { case n { S[p] → p } }

// Predecessor function with value zero in zero.
val full_pred : nat ⇒ nat =
  fun n { case n { 0 → 0 | S[n] → n } }

// Test to zero.
val is_zero : nat ⇒ bool =
  fun n { case n { 0 → true | S[_] → false } }

// Addition function.
infix (+) = add priority 3 left associative

val rec (+) : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      0    → m
      S[k] → succ (k + m)
    }
  }

// Multiplication function.
infix (*) = mul priority 2 left associative

val rec (*) : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      0    → 0
      S[k] → m + (k * m)
    }
  }

// Exponentiation function.
infix (**) = exp priority 1 right associative

val rec (**) : nat ⇒ nat ⇒ nat =
  fun n m {
    case m {
      0    → 1
      S[k] → n * (n ** k)
    }
  }

// Difference function.
infix (-) = minus priority 3 left associative

val rec (-) : ∀s, nat^s ⇒ nat ⇒ nat^s =
  fun n m {
    case n {
      0    → 0
      S[p] → case m {
        0    → n
        S[q] → p - q
      }
    }
  }

//// Comparison and equality /////////////////////////////////////////////////
include lib.comparison

// Comparison function.
val rec compare : ∀n m∈nat, dcmp⟨n,m⟩ =
  fun n m {
    case n {
      0    → case m {
        0    → Eq
        S[_] → Ls
      }
      S[n] → case m {
        0    → Gr
        S[m] → compare n m
      }
    }
  }

// Equality function.
val eq : nat ⇒ nat ⇒ bool =
  fun n m { case compare n m { Ls → false | Eq → true  | Gr → false } }

val neq : nat ⇒ nat ⇒ bool =
  fun n m { case compare n m { Ls → true  | Eq → false | Gr → true  } }

val leq : nat ⇒ nat ⇒ bool =
  fun n m { case compare n m { Ls → true  | Eq → true  | Gr → false } }

val lt : nat ⇒ nat ⇒ bool =
  fun n m { case compare n m { Ls → true  | Eq → false | Gr → false } }

val geq : nat ⇒ nat ⇒ bool =
  fun n m { case compare n m { Ls → false | Eq → true  | Gr → true  } }

val gt : nat ⇒ nat ⇒ bool =
  fun n m { case compare n m { Ls → false | Eq → false | Gr → true  } }

infix (≤) = leq priority 5 non associative
infix (<) = lt priority 5 non associative
infix (≥) = geq priority 5 non associative
infix (>) = gt priority 5 non associative

val min : nat ⇒ nat ⇒ nat =
  fun n m { if n ≤ m { n } else { m } }

val max : nat ⇒ nat ⇒ nat =
  fun n m { if n ≤ m { m } else { n } }

//// More functions //////////////////////////////////////////////////////////

// Ackermann's function.
val rec ack : nat ⇒ nat ⇒ nat =
  fun m n {
    case m {
      0    → succ n
      S[p] → case n {
        0    → ack p 1
        S[q] → ack p (ack m q)
      }
    }
  }

// Factorial function.
val rec fact : nat ⇒ nat =
  fun n {
    case n {
      0    → zero
      S[k] → case k {
        0    → 1
        S[_] → n * (fact k)
      }
    }
  }

// Print a natural number.
val rec print_nat : nat ⇒ {} =
  fun n {
    case n {
      0    → print "0"
      S[k] → print "S"; print_nat k
    }
  }

// Print a natural number with a newline.
val println_nat : nat ⇒ {} =
  fun n { print_nat n; print "\n" }

include lib.either

// sub_size n S[m]
//    either return n with a sized type less or equal than the size of m
//    or return n - S[m] with a sized type less that the size of n

val rec sub_size : ∀o1 o2, ∀n∈nat^(o1+ₒ1), ∀m∈[S of nat^o2],
                     either⟨n∈nat^o2 | n < m, {p∈nat^o1 | n ≡ m + p}⟩ =
  fun n m {
    case m {
      S[m'] →
        let rec sub_aux : ∀o1 o2, ∀n∈nat^(o1+ₒ1), ∀m∈nat^o2,
                      either⟨n∈nat^o2 | n < S[m], {p∈nat^o1 | n ≡ S[m] + p}⟩ =
          fun n m {
            case n {
              0     → InL[Zero]
              S[n'] →
                case m {
                  0     → InR[n']
                  S[m'] →
                    case sub_aux n' m' {
                      InL[r] → InL[S[r]]
                      InR[d] → InR[d]
                    }
                }
            }
          };
        sub_aux n m'
    }
  }

// modulo, with size information
infix (%) = mod priority 2 left associative

val rec (%) : ∀o, nat ⇒ [S of nat^o] ⇒ nat^o =
  fun n m {
    case sub_size n m {
      InL[r]  → r
      InR[n'] →
        case n' {
          0      → Zero
          S[n''] → n' % m
        }
    }
  }


infix (/) = div priority 2 left associative

// div
val rec (/) : nat ⇒ [S of nat] ⇒ nat =
  fun n m {
    case sub_size n m {
      InL[r]  → 0
      InR[n'] →
        case n' {
          0      → 1
          S[n''] → S[n' / m]
        }
    }
  }

// gcd. Note: if we add a max on ord, we could have the size information
val rec gcd : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      0     → m
      S[n'] →
        case m {
          0     → n
          S[m'] → gcd (m % S[n']) n
            }
        }
    }
