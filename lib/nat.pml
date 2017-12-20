// Unary natural numbers.

// The type of unary natural numbers.
type rec nat = [Zero ; S of nat]

// Smart constructors for zero and the successor.
val zero : nat = Zero
val succ : nat ⇒ nat = fun n { S[n] }

// Usual numbers.
val one : nat = succ zero
val two : nat = succ one

//// Usual operations ////////////////////////////////////////////////////////

// Predecessor function for non-zero numbers.
val pred : [S of nat] ⇒ nat = fun n { case n { S[p] → p } }

// Predecessor function with value zero in zero.
val full_pred : nat ⇒ nat =
  fun n { case n { Zero → zero | S[n] → n } }

// Test to zero.
val is_zero : nat ⇒ bool =
  fun n { case n { Zero → true | S[_] → false } }

// Addition function.
infix (+) = add priority 3 left associative

val rec (+) : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero → m
      S[k] → succ (k + m)
    }
  }

// Multiplication function.
infix (*) = mul priority 2 left associative

val rec ( * ) : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero → zero
      S[k] → m + (k * m)
    }
  }

// Exponentiation function.
infix (**) = exp priority 1 right associative

val rec ( ** ) : nat ⇒ nat ⇒ nat =
  fun n m {
    case m {
      Zero → one
      S[k] → n * (n ** k)
    }
  }

// Minus function.
infix (-) = minus priority 3 right associative

val rec (-) : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero → zero
      S[p] → case m {
        Zero → n
        S[q] → p - q
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
val u1000 : nat = mul u10 u100

//// Comparison and equality /////////////////////////////////////////////////
include lib.comparison

// Comparison function.
val rec compare : ∀n m∈nat, dcmp<n,m> =
  fun n m {
    case n {
      Zero → case m {
        Zero → Eq
        S[_] → Ls
      }
      S[n] → case m {
        Zero → Gr
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
      Zero → succ n
      S[p] → case n {
        Zero → ack p one
        S[q] → ack p (ack m q)
      }
    }
  }

// Factorial function.
val rec fact : nat ⇒ nat =
  fun n {
    case n {
      Zero → zero
      S[k] → case k {
        Zero → one
        S[_] → n * (fact k)
      }
    }
  }

// Print a natural number.
val rec print_nat : nat ⇒ {} =
  fun n {
    case n {
      Zero → print "0"
      S[k] → print "S"; print_nat k
    }
  }

// Print a natural number with a newline.
val println_nat : nat ⇒ {} =
  fun n { print_nat n; print "\n" }
