// Unary natural numbers.

// The type of unary natural numbers.
type rec nat = [Zero ; S of nat]

// Smart constructors for zero and the successor.
val zero : nat = Zero
val succ : nat ⇒ nat = fun n { S[n] }

// With dble can use natural numbers!
val rec dble : nat ⇒ nat = fun n { case n { Zero → Zero | S[p] → S[S[dble p]] }}

// Usual numbers.
val one : nat = 1
val two : nat = 2

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
      Zero → 0
      S[k] → m + (k * m)
    }
  }

// Exponentiation function.
infix (**) = exp priority 1 right associative

val rec ( ** ) : nat ⇒ nat ⇒ nat =
  fun n m {
    case m {
      Zero → 1
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
        Zero → ack p 1
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
        Zero → 1
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
