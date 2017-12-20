// Proofs on unary natural numbers.

include lib.nat

//// Properties of addition //////////////////////////////////////////////////

// Associativity of addition (detailed proof).
val rec add_assoc : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  fun m n p {
    case m {
      Zero → eqns 0 + (n + p)
                     ≡ n + p
                     ≡ (0 + n) + p
      S[k] → eqns m + (n + p)
                    ≡ S[k] + (n + p)
                    ≡ S[k + (n + p)]
                    ≡ S[(k + n) + p] by add_assoc k n p
                    ≡ S[k + n] + p
                    ≡ (S[k] + n) + p
                    ≡ (m + n) + p
    }
  }

// Associativity of addition (shortest proof).
val rec add_assoc2 : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  fun m n p {
    case m {
      Zero → qed
      S[k] → use add_assoc2 k n p; qed
    }
  }

// Zero as a neutral element on the right (detailed proof).
val rec add_n_zero : ∀n∈nat, n + 0 ≡ n =
  fun n {
    case n {
      Zero → qed
      S[k] → eqns n + 0 ≡ S[k] + 0 ≡ S[k + 0]
                         ≡ S[k] by add_n_zero k ≡ n
    }
  }

// Successor on the right can be taken out (detailed proof).
val rec add_n_succ : ∀m n∈nat, m + S[n] ≡ S[m + n] =
  fun m n {
    case m {
      Zero → qed
      S[k] → eqns m + S[n] ≡ S[k + S[n]]
                           ≡ S[S[k + n]] by add_n_succ k n
                           ≡ S[m + n]
    }
  }

// Commutativity of addition (detailed proof).
val rec add_comm : ∀m n∈nat, m + n ≡ n + m =
  fun m n {
    case m {
      Zero → eqns 0 + n ≡ n ≡ n + 0 by add_n_zero n
      S[k] → eqns m + n ≡ S[k + n]
                        ≡ S[n + k]    by add_comm k n
                        ≡ n + m       by add_n_succ n k
    }
  }

//// Properties of multiplication ////////////////////////////////////////////

// Zero as an absorbing element on the right (detailed proof).
val rec mul_n_zero : ∀n∈nat, n * 0 ≡ 0 =
  fun n {
    case n {
      Zero → deduce 0 * 0 ≡ 0;
             qed
      S[k] → show k * 0 ≡ 0 using mul_n_zero k;
             deduce 0 + k * 0 ≡ 0;
             qed
    }
  }

val rec mul_neutral : ∀n∈nat, 1 * n ≡ n =
  fun n { add_n_zero n }

// Successor on the right can be taken out (detailed proof).
val rec mul_n_succ : ∀n m∈nat, n * S[m] ≡ n + n * m =
  fun n m {
    case n {
      Zero → deduce 0 * S[m] ≡ 0 + 0 * m;
             qed
      S[k] → show k * S[m] ≡ k + k * m using mul_n_succ k m;
             deduce S[m] + k * S[m] ≡ S[m] + (k + k * m);
             deduce n * S[m] ≡ S[m] + (k + k * m);
             deduce n * S[m] ≡ S[m + (k + k * m)];
             show m + (k + k * m) ≡ (m + k) + k * m using add_assoc m k (k * m);
             show m + k ≡ k + m using add_comm m k;
             show m + (k + k * m) ≡ k + (m + k * m) using add_assoc k m (k * m);
             deduce n * S[m] ≡ S[k + (m + k * m)];
             deduce n * S[m] ≡ S[k + n * m];
             deduce n * S[m] ≡ n + n * m;
             qed
    }
  }

// Multiplication is commutative (detailed proof).
val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero → deduce mul 0 m ≡ 0;
             show mul m 0 ≡ 0 using mul_n_zero m;
             deduce mul 0 m ≡ mul m 0;
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
      Zero → deduce mul 0 (add n p) ≡ 0;
             deduce add (mul 0 n) (mul 0 p) ≡ 0;
             deduce mul 0 (add n p) ≡ add (mul 0 n) (mul 0 p);
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
      Zero → showing mul 0 (mul n p) ≡ mul (mul 0 n) p;
             deduce mul 0 (mul n p) ≡ 0;
             showing 0 ≡ mul (mul 0 n) p;
             deduce mul (mul 0 n) p ≡ mul 0 p;
             deduce mul (mul 0 n) p ≡ 0;
             showing 0 ≡ 0;
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
