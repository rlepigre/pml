// Unary natural numbers.

// The type of unary natural numbers.
type rec nat = [Z ; S of nat]

// Smart constructors for zero and the successor.
val zero : nat = Z
val succ : nat ⇒ nat = fun n { S[n] }

// Usual numbers.
val one : nat = succ zero
val two : nat = succ one

//// Usual operations ////////////////////////////////////////////////////////

// Predecessor function for non-zero numbers.
val pred : [S of nat] ⇒ nat = fun n { case n { S[p] → p } }

// Predecessor function with value zero in zero.
val full_pred : nat ⇒ nat =
  fun n { case n { Z → zero | S[n] → n } }

// Test to zero.
val is_zero : nat ⇒ bool =
  fun n { case n { Z → true | S[_] → false } }

// Addition function.
val rec add : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Z    → m
      S[k] → succ (add k m)
    }
  }

// Multiplication function.
val rec mul : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Z    → zero
      S[k] → add m (mul k m)
    }
  }

// Exponentiation function.
val rec exp : nat ⇒ nat ⇒ nat =
  fun n m {
    case m {
      Z    → one
      S[k] → mul n (exp n k)
    }
  }

// Minus function.
val rec minus : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Z    → zero
      S[p] → case m {
        Z    → n
        S[q] → minus p q
      }
    }
  }

//// Number constants ////////////////////////////////////////////////////////

val u0   : nat = zero
val u1   : nat = succ u0
val u2   : nat = succ u1
val u3   : nat = succ u2
val u4   : nat = succ u3
val u5   : nat = succ u4
val u6   : nat = succ u5
val u7   : nat = succ u6
val u8   : nat = succ u7
val u9   : nat = succ u8
val u10  : nat = succ u9
val u11  : nat = succ u10
val u90  : nat = mul u10 u9
val u91  : nat = succ u90
val u100 : nat = mul u10 u10
val u101 : nat = succ u100

//// Comparison and equality /////////////////////////////////////////////////

// Comparison function.
val rec compare : nat ⇒ nat ⇒ [Ls ; Eq ; Gr] =
  fun n m {
    case n {
      Z    → case m {
        Z    → Eq
        S[_] → Ls
      }
      S[n] → case m {
        Z    → Gr
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


//// More functions //////////////////////////////////////////////////////////

// Ackermann's function.
val rec ack : nat ⇒ nat ⇒ nat =
  fun m n {
    case m {
      Z    → succ n
      S[p] → case n {
        Z    → ack p one
        S[q] → ack p (ack m q)
      }
    }
  }

// Factorial function.
val rec fact : nat ⇒ nat =
  fun n {
    case n {
      Z    → zero
      S[k] → case k {
        Z    → one
        S[_] → mul n (fact k)
      }
    }
  }

// Print a natural number.
val rec print_nat : nat ⇒ {} =
  fun n {
    case n {
      Z    → print "Z"
      S[k] → print "S"; print_nat k
    }
  }

// Print a natural number with a newline.
val println_nat : nat ⇒ {} =
  fun n { print_nat n; print "\n" }
