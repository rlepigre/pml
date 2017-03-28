// Unary natural numbers and their usual properties.

// The type of unary natural numbers.
type rec nat = [Z ; S of nat]

// Smart constructors for zero and the successor.
val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

// Usual numbers.
val one : nat = succ zero
val two : nat = succ one

//// Usual operations ////////////////////////////////////////////////////////

// Predecessor function for non-zero numbers.
val pred : [S of nat] ⇒ nat = fun n →
  case n { S[n] → n }

// Predecessor function with value zero in zero.
val full_pred : nat ⇒ nat = fun n →
  case n { Z[_] → zero | S[n] → n }

// Test to zero.
val is_zero : nat ⇒ bool = fun n →
  case n { Z[_] → true | S[_] → false }

// Addition function.
val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    Z[_] → m
    S[k] → succ (add k m)
  }

// Multiplication funtion.
val rec mul : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    Z[_] → zero
    S[k] → add m (mul k m)
  }

// Exponentiation function.
val rec exp : nat ⇒ nat ⇒ nat = fun n m →
  case m {
    Z[_] → one
    S[k] → mul n (exp n k)
  }

// Minus function.
val rec minus : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    Z[_] → zero
    S[p] → case m {
             Z[_] → n
             S[q] → minus p q
           }
  }

//// Comparison and equality /////////////////////////////////////////////////

// Comparison function.
val rec compare : nat ⇒ nat ⇒ [Ls ; Eq ; Gr] = fun n m →
  case n {
    Z[_] → case m {
             Z[_] → Eq
             S[_] → Ls
           }
    S[n] → case m {
             Z[_] → Gr
             S[m] → compare n m
           }
  }

// Equality function.
val eq : nat ⇒ nat ⇒ bool = fun n m →
  case compare n m {
    Ls[_] → false
    Eq[_] → true
    Gr[_] → false
  }

//// More functions //////////////////////////////////////////////////////////

// Ackermann's function.
val rec ack : nat ⇒ nat ⇒ nat = fun m n →
  case m {
    Z[_] → succ n
    S[p] → case n {
             Z[_] → ack p one
             S[q] → ack p q
           }
  }

// Factorial function.
val rec fact : nat ⇒ nat = fun n →
  case n {
    Z[_] → zero
    S[k] → case k {
             Z[_] → one
             S[_] → mul n (fact k)
           }
  }

//// Properties of addition //////////////////////////////////////////////////

// Totality of addition.
val rec add_total : ∀n m∈nat, ∃v:ι↓, add n m ≡ v = fun n m →
  case n {
    Z[_] → qed
    S[k] → use add_total k m; qed
  }

// Associativity of addition (detailed proof).
val rec add_assoc : ∀m n p∈nat, add m (add n p) ≡ add (add m n) p =
  fun m n p →
    use add_total n p;
    case m {
      Z[_] → deduce add n p ≡ add (add Z n) p;
             deduce add Z (add n p) ≡ add (add Z n) p;
             qed
      S[k] → show add k (add n p) ≡ add (add k n) p using add_assoc k n p;
             deduce S[add k (add n p)] ≡ S[add (add k n) p];
             deduce add S[k] (add n p) ≡ S[add (add k n) p];
             use add_total k n;
             deduce add S[k] (add n p) ≡ add S[add k n] p;
             deduce add S[k] (add n p) ≡ add (add S[k] n) p;
             qed
    }

// Zero as a neutral element on the right (detailed proof).
val rec add_n_zero : ∀n∈nat, add n zero ≡ n = fun n →
  case n {
    Z[_] → deduce add Z Z ≡ Z;
           deduce Z ≡ Z;
           qed
    S[k] → show add k Z ≡ k using add_n_zero k;
           deduce S[add k Z] ≡ S[k];
           deduce add S[k] Z ≡ S[k];
           qed
  }

// Successor on the right can be taken out (detailed proof).
val rec add_n_succ : ∀m n∈nat, add m S[n] ≡ S[add m n] = fun m n →
  case m {
    Z[_] → deduce add Z S[n] ≡ S[add Z n];
           qed
    S[k] → show add k S[n] ≡ S[add k n] using add_n_succ k n;
           deduce S[add k S[n]] ≡ S[S[add k n]];
           deduce add S[k] S[n] ≡ S[S[add k n]];
           deduce add S[k] S[n] ≡ S[add S[k] n];
           qed
  }

// Commutativity of addition (detailed proof).
val rec add_comm : ∀m n∈nat, add m n ≡ add n m = fun m n →
  case m {
    Z[_] → show add n Z ≡ add Z n using add_n_zero n;
           deduce add Z n ≡ add n Z;
           qed
    S[k] → show add k n ≡ add n k using add_comm k n;
           deduce S[add k n] ≡ S[add n k];
           show S[add k n] ≡ add n S[k] using add_n_succ n k;
           deduce add S[k] n ≡ add n S[k];
           qed
  }

//// Properties of multiplication ////////////////////////////////////////////

// Totality of multiplication.
val rec mul_total : ∀n m∈nat, ∃v:ι↓, mul n m ≡ v = fun n m →
  case n {
    Z[_] → qed
    S[k] → use mul_total k m;
           use add_total m (mul k m)
  }

// Zero as an absorbing element on the right (detailed proof).
val rec mul_n_zero : ∀n∈nat, mul n Z ≡ Z = fun n →
  case n {
    Z[_] → deduce mul Z Z ≡ Z;
           qed
    S[k] → show mul k Z ≡ Z using mul_n_zero k;
           deduce add Z (mul k Z) ≡ Z;
           qed
  }
