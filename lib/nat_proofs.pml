// Proofs on unary natural numbers.

include lib.nat

//// Properties of addition //////////////////////////////////////////////////

// Associativity of addition (detailed proof).
val rec add_assoc : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  fun m n p {
    case m {
      Zero → showing u0 + (n + p) ≡ u0 + n + p;
             deduce n + p ≡ u0 + n + p;
             deduce u0 + (n + p) ≡ (u0 + n + p);
             qed
      S[k] → show k + (n + p) ≡ (k + n) + p using add_assoc k n p;
             deduce S[k + (n + p)] ≡ S[(k + n) + p];
             deduce S[k] + (n + p) ≡ S[(k + n) + p];
             deduce S[k] + (n + p) ≡ S[k + n] + p;
             deduce S[k] + (n + p) ≡ (S[k] + n) + p;
             qed
    }
  }

// Associativity of addition (shortest proof).
val rec add_assoc2 : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  fun m n p {
    case m {
      Zero → qed
      S[k] → use add_assoc2 k n p;  qed
    }
  }

// Zero as a neutral element on the right (detailed proof).
val rec add_n_zero : ∀n∈nat, n + u0 ≡ n =
  fun n {
    case n {
      Zero → deduce u0 + u0 ≡ u0;
             qed
      S[k] → show k + u0 ≡ k using add_n_zero k;
             deduce S[k + u0] ≡ S[k];
             deduce S[k] + u0 ≡ S[k];
             qed
    }
  }

// Successor on the right can be taken out (detailed proof).
val rec add_n_succ : ∀m n∈nat, m + S[n] ≡ S[m + n] =
  fun m n {
    case m {
      Zero → deduce add u0 S[n] ≡ S[u0 + n];
             qed
      S[k] → show k + S[n] ≡ S[k + n] using add_n_succ k n;
             deduce S[k + S[n]] ≡ S[S[k + n]];
             deduce add S[k] S[n] ≡ S[S[add k n]];
             deduce add S[k] S[n] ≡ S[add S[k] n];
             deduce add S[k] S[n] ≡ S[S[add k n]];
             qed
    }
  }

// Commutativity of addition (detailed proof).
val rec add_comm : ∀m n∈nat, add m n ≡ add n m =
  fun m n {
    case m {
      Zero → show add n u0 ≡ add u0 n using add_n_zero n;
             deduce add u0 n ≡ add n u0;
             qed
      S[k] → show add k n ≡ add n k using add_comm k n;
             deduce S[add k n] ≡ S[add n k];
             show S[add k n] ≡ add n S[k] using add_n_succ n k;
             deduce add S[k] n ≡ add n S[k];
             qed
    }
  }

//// Properties of multiplication ////////////////////////////////////////////

// Zero as an absorbing element on the right (detailed proof).
val rec mul_n_zero : ∀n∈nat, mul n u0 ≡ u0 =
  fun n {
    case n {
      Zero → deduce mul u0 u0 ≡ u0;
             qed
      S[k] → show mul k u0 ≡ u0 using mul_n_zero k;
             deduce add u0 (mul k u0) ≡ u0;
             qed
    }
  }

val rec mul_neutral : ∀n∈nat, mul u1 n ≡ n =
  fun n { add_n_zero n }

// Successor on the right can be taken out (detailed proof).
val rec mul_n_succ : ∀n m∈nat, mul n S[m] ≡ add n (mul n m) =
  fun n m {
    case n {
      Zero → deduce mul u0 S[m] ≡ add u0 (mul u0 m);
             qed
      S[k] → show mul k S[m] ≡ add k (mul k m) using mul_n_succ k m;
             deduce add S[m] (mul k S[m]) ≡ add S[m] (add k (mul k m));
             deduce mul S[k] S[m] ≡ add S[m] (add k (mul k m));
             deduce mul S[k] S[m] ≡ S[add m (add k (mul k m))];
             show add m (add k (mul k m)) ≡ add (add m k) (mul k m)
               using add_assoc m k (mul k m);
             show add m k ≡ add k m using add_comm m k;
             show add m (add k (mul k m)) ≡ add k (add m (mul k m))
               using add_assoc k m (mul k m);
             deduce mul S[k] S[m] ≡ S[add k (add m (mul k m))];
             deduce mul S[k] S[m] ≡ S[add k (mul S[k] m)];
             deduce mul S[k] S[m] ≡ add S[k] (mul S[k] m);
             qed
    }
  }

// Multiplication is commutative (detailed proof).
val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero → deduce mul u0 m ≡ u0;
             show mul m u0 ≡ u0 using mul_n_zero m;
             deduce mul u0 m ≡ mul m u0;
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
      Zero → deduce mul u0 (add n p) ≡ u0;
             deduce add (mul u0 n) (mul u0 p) ≡ u0;
             deduce mul u0 (add n p) ≡ add (mul u0 n) (mul u0 p);
             qed
      S[k] → showing mul m (add n p) ≡ add (mul m n) (mul m p);
             show mul k (add n p) ≡ add (mul k n) (mul k p)
               using mul_dist_l k n p;
             deduce add (add n p) (mul k (add n p))
               ≡ add (add n p) (add (mul k n) (mul k p));
             deduce mul S[k] (add n p)
               ≡ add (add n p) (add (mul k n) (mul k p));
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
      Zero → showing mul u0 (mul n p) ≡ mul (mul u0 n) p;
             deduce mul u0 (mul n p) ≡ u0;
             showing u0 ≡ mul (mul u0 n) p;
             deduce mul (mul u0 n) p ≡ mul u0 p;
             deduce mul (mul u0 n) p ≡ u0;
             showing u0 ≡ u0;
             qed
      S[k] → show mul k (mul n p) ≡ mul (mul k n) p using mul_assoc k n p;
             deduce add (mul n p) (mul k (mul n p))
               ≡ add (mul n p) (mul (mul k n) p);
             deduce mul S[k] (mul n p) ≡ add (mul n p) (mul (mul k n) p);
             show add (mul n p) (mul (mul k n) p) ≡ mul (add n (mul k n)) p
               using mul_dist_r n (mul k n) p;
             deduce mul S[k] (mul n p) ≡ mul (add n (mul k n)) p;
             deduce mul S[k] (mul n p) ≡ mul (mul S[k] n) p;
             qed
    }
  }

include lib.comparison

val rec succ_gr : ∀n m∈nat, compare n m ≡ Gr ⇒ compare S[n] m ≡ Gr =
  fun n m h {
    case n {
      Zero →
        case m {
          Zero → ✂
          S[l] → ✂
        }
      S[k] →
        case m {
          Zero → qed
          S[l] → deduce compare k l ≡ Gr;
                 use succ_gr k l {}; qed
        }
    }
  }

val rec succ_ls : ∀n m∈nat, compare n m ≡ Ls ⇒ compare n S[m] ≡ Ls =
  fun n m h {
    case n {
      Zero → {}
      S[k] →
        case m {
          Zero → ✂
          S[l] → deduce compare k l ≡ Ls;
                 use succ_ls k l {}; qed
        }
    }
  }

val rec succ_eq_r : ∀n m∈nat, compare n m ≡ Eq ⇒ compare n S[m] ≡ Ls =
  fun n m h {
    case n {
      Zero →
        case m {
          Zero → {}
          S[l] → ✂
        }
      S[k] →
        case m {
          Zero → ✂
          S[l] → deduce compare k l ≡ Eq;
                 use succ_eq_r k l {}; qed
        }
    }
  }

val rec compare_eq : ∀n m∈nat, compare n m ≡ Eq ⇒ n ≡ m =
  fun n m h {
    case n {
      Zero →
        case m {
          Zero → {}
          S[l] → ✂
        }
      S[k] →
        case m {
          Zero → ✂
          S[l] → deduce compare k l ≡ Eq;
                 use compare_eq k l {}; qed
        }
    }
  }
