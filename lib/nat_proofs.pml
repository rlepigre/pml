// Proofs on unary natural numbers.

include lib.nat

//// Properties of addition //////////////////////////////////////////////////

// Totality of addition.
val rec add_total : ∀n m∈nat, ∃v:ι, add n m ≡ v =
  fun n m {
    case n {
      Z    → qed
      S[k] → use add_total k m; qed
    }
  }

// Associativity of addition (detailed proof).
val rec add_assoc : ∀m n p∈nat, add m (add n p) ≡ add (add m n) p =
  fun m n p {
    use add_total n p;
    case m {
      Z    → deduce add n p ≡ add (add Z n) p;
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
  }

// Associativity of addition (shortest proof).
val rec add_assoc2 : ∀m n p∈nat, add m (add n p) ≡ add (add m n) p =
  fun m n p {
    use add_total n p;
    case m {
      Z    → qed
      S[k] → use add_assoc2 k n p;
             use add_total k n;
             qed
    }
  }

// Zero as a neutral element on the right (detailed proof).
val rec add_n_zero : ∀n∈nat, add n zero ≡ n =
  fun n {
    case n {
      Z    → deduce add Z Z ≡ Z;
             qed
      S[k] → show add k Z ≡ k using add_n_zero k;
             deduce S[add k Z] ≡ S[k];
             deduce add S[k] Z ≡ S[k];
             qed
    }
  }

// Successor on the right can be taken out (detailed proof).
val rec add_n_succ : ∀m n∈nat, add m S[n] ≡ S[add m n] =
  fun m n {
    case m {
      Z    → deduce add Z S[n] ≡ S[add Z n];
             qed
      S[k] → show add k S[n] ≡ S[add k n] using add_n_succ k n;
             deduce S[add k S[n]] ≡ S[S[add k n]];
             deduce add S[k] S[n] ≡ S[S[add k n]];
             deduce add S[k] S[n] ≡ S[add S[k] n];
             qed
    }
  }

// Commutativity of addition (detailed proof).
val rec add_comm : ∀m n∈nat, add m n ≡ add n m =
  fun m n {
    case m {
      Z    → show add n Z ≡ add Z n using add_n_zero n;
             deduce add Z n ≡ add n Z;
             qed
      S[k] → show add k n ≡ add n k using add_comm k n;
             deduce S[add k n] ≡ S[add n k];
             show S[add k n] ≡ add n S[k] using add_n_succ n k;
             deduce add S[k] n ≡ add n S[k];
             qed
    }
  }

//// Properties of multiplication ////////////////////////////////////////////

// Totality of multiplication.
val rec mul_total : ∀n m∈nat, ∃v:ι, mul n m ≡ v =
  fun n m {
    case n {
      Z    → qed
      S[k] → use mul_total k m;
             use add_total m (mul k m)
    }
  }

// Zero as an absorbing element on the right (detailed proof).
val rec mul_n_zero : ∀n∈nat, mul n Z ≡ Z =
  fun n {
    case n {
      Z    → deduce mul Z Z ≡ Z;
             qed
      S[k] → show mul k Z ≡ Z using mul_n_zero k;
             deduce add Z (mul k Z) ≡ Z;
             qed
    }
  }

// Successor on the right can be taken out (detailed proof).
val rec mul_n_succ : ∀n m∈nat, mul n S[m] ≡ add n (mul n m) =
  fun n m {
    case n {
      Z    → deduce mul Z S[m] ≡ add Z (mul Z m);
             qed
      S[k] → show mul k S[m] ≡ add k (mul k m) using mul_n_succ k m;
             deduce add S[m] (mul k S[m]) ≡ add S[m] (add k (mul k m));
             use mul_total k S[m];
             deduce mul S[k] S[m] ≡ add S[m] (add k (mul k m));
             deduce mul S[k] S[m] ≡ S[add m (add k (mul k m))];
             use mul_total k m;
             show add m (add k (mul k m)) ≡ add (add m k) (mul k m)
               using add_assoc m k (mul k m);
             show add m k ≡ add k m using add_comm m k;
             show add m (add k (mul k m)) ≡ add k (add m (mul k m))
               using add_assoc k m (mul k m);
             deduce mul S[k] S[m] ≡ S[add k (add m (mul k m))];
             deduce mul S[k] S[m] ≡ S[add k (mul S[k] m)];
             use mul_total S[k] m;
             deduce mul S[k] S[m] ≡ add S[k] (mul S[k] m);
             qed
    }
  }

// Multiplication is commutative (detailed proof).
val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Z    → deduce mul Z m ≡ Z;
             show mul m Z ≡ Z using mul_n_zero m;
             deduce mul Z m ≡ mul m Z;
             qed
      S[k] → show mul k m ≡ mul m k using mul_comm k m;
             deduce add m (mul k m) ≡ add m (mul m k);
             deduce mul S[k] m ≡ add m (mul m k);
             show mul m S[k] ≡ add m (mul k m) using mul_n_succ m k;
             deduce mul S[k] m ≡ mul m S[k];
             qed
    }
  }

// Left distributivity of multiplication over addition (detailed proof).
val rec mul_dist_l : ∀m n p∈nat, mul m (add n p) ≡ add (mul m n) (mul m p) =
  fun m n p {
    case m {
      Z    → use add_total n p;
             deduce mul Z (add n p) ≡ Z;
             deduce add (mul Z n) (mul Z p) ≡ Z;
             deduce mul Z (add n p) ≡ add (mul Z n) (mul Z p);
             qed
      S[k] → show mul k (add n p) ≡ add (mul k n) (mul k p)
               using mul_dist_l k n p;
             deduce add (add n p) (mul k (add n p))
               ≡ add (add n p) (add (mul k n) (mul k p));
             use add_total n p;
             deduce mul S[k] (add n p)
               ≡ add (add n p) (add (mul k n) (mul k p));
             use mul_total k n;
             use mul_total k p;
             use add_total (mul k n) (mul k p);
             show add (add n p) (add (mul k n) (mul k p))
               ≡ add n (add p (add (mul k n) (mul k p)))
               using add_assoc n p (add (mul k n) (mul k p));
             show add p (add (mul k n) (mul k p))
               ≡ add (add p (mul k n)) (mul k p)
               using add_assoc p (mul k n) (mul k p);
             show add p (mul k n) ≡ add (mul k n) p
               using add_comm p (mul k n);
             deduce add (add n p) (add (mul k n) (mul k p))
               ≡ add n (add (add (mul k n) p) (mul k p));
             show add (add (mul k n) p) (mul k p)
               ≡ add (mul k n) (add p (mul k p))
               using add_assoc (mul k n) p (mul k p);
             deduce add (add n p) (add (mul k n) (mul k p))
               ≡ add n (add (mul k n) (add p (mul k p)));
             deduce add (add n p) (add (mul k n) (mul k p))
               ≡ add n (add (mul k n) (mul S[k] p));
             use mul_total S[k] p;
             show add n (add (mul k n) (mul S[k] p))
               ≡ add (add n (mul k n)) (mul S[k] p)
               using add_assoc n (mul k n) (mul S[k] p);
             deduce add (add n p) (add (mul k n) (mul k p))
               ≡ add (mul S[k] n) (mul S[k] p);
             qed
    }
  }

// Right distributivity of multiplication over addition (detailed proof).
val rec mul_dist_r : ∀m n p∈nat, mul (add m n) p ≡ add (mul m p) (mul n p) =
  fun m n p {
    show mul p (add m n) ≡ add (mul p m) (mul p n) using mul_dist_l p m n;
    use add_total m n;
    show mul p (add m n) ≡ mul (add m n) p using mul_comm p (add m n);
    deduce mul (add m n) p ≡ add (mul p m) (mul p n);
    show mul p m ≡ mul m p using mul_comm p m;
    deduce mul (add m n) p ≡ add (mul m p) (mul p n);
    show mul p n ≡ mul n p using mul_comm p n;
    deduce mul (add m n) p ≡ add (mul m p) (mul n p);
    qed
  }

// Associativity of multiplication (detailed proof).
val rec mul_assoc : ∀m n p∈nat, mul m (mul n p) ≡ mul (mul m n) p =
  fun m n p {
    case m {
      Z    → use mul_total n p;
             deduce mul Z (mul n p) ≡ Z;
             deduce mul (mul Z n) p ≡ mul Z p;
             deduce mul (mul Z n) p ≡ Z;
             deduce mul Z (mul n p) ≡ mul (mul Z n) p;
             qed
      S[k] → show mul k (mul n p) ≡ mul (mul k n) p using mul_assoc k n p;
             deduce add (mul n p) (mul k (mul n p))
               ≡ add (mul n p) (mul (mul k n) p);
             use mul_total n p;
             deduce mul S[k] (mul n p) ≡ add (mul n p) (mul (mul k n) p);
             use mul_total k n;
             show add (mul n p) (mul (mul k n) p) ≡ mul (add n (mul k n)) p
               using mul_dist_r n (mul k n) p;
             deduce mul S[k] (mul n p) ≡ mul (add n (mul k n)) p;
             deduce mul S[k] (mul n p) ≡ mul (mul S[k] n) p;
             qed
    }
  }

val rec compare_total : ∀x y∈nat, ∃v:ι, compare x y ≡ v =
  fun x y {
    case x {
      Z    → case y {
               Z    → {}
               S[_] → {}
             }
      S[x] → case y {
               Z    → {}
               S[y] → compare_total x y
             }
    }
  }

def compare_total_common =
  fun x y {
    use compare_total x y;
    case compare x y { Ls → {} | Eq → {} | Gr → {} }
  }

val  eq_total : ∀x y∈nat, ∃v:ι,  eq x y ≡ v = compare_total_common
val neq_total : ∀x y∈nat, ∃v:ι, neq x y ≡ v = compare_total_common
val leq_total : ∀x y∈nat, ∃v:ι, leq x y ≡ v = compare_total_common
val  lt_total : ∀x y∈nat, ∃v:ι,  lt x y ≡ v = compare_total_common
val geq_total : ∀x y∈nat, ∃v:ι, geq x y ≡ v = compare_total_common
val  gt_total : ∀x y∈nat, ∃v:ι,  gt x y ≡ v = compare_total_common
