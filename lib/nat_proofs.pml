// Proofs on unary natural numbers.

include lib.nat
include lib.bool

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
                    ≡ S[k + n] + p;
             eqns (m + n) + p
                    ≡ (S[k] + n) + p
                    ≡ S[k + n] + p;
             qed
    }
  }

// Associativity of addition (shortest proof).
val rec add_assoc2 : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  fun m n p {
    case m {
      Zero → qed
      S[k] → add_assoc2 k n p
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
      Zero → eqns 0 * 0 ≡ 0
      S[k] → eqns S[k] * 0 ≡ 0 + k * 0
                           ≡ 0 + 0 by mul_n_zero k
                           ≡ 0
    }
  }

val rec mul_neutral : ∀n∈nat, 1 * n ≡ n =
  fun n { add_n_zero n }

// Successor on the right can be taken out (detailed proof).
val rec mul_n_succ : ∀n m∈nat, n * S[m] ≡ n + n * m =
  fun n m {
    case n {
      Zero → eqns 0 * S[m] ≡ 0 + 0 * m ≡ 0
      S[k] → eqns n * S[m] ≡ S[m] + k * S[m]
                           ≡ S[m] + (k + k * m) by mul_n_succ k m
                           ≡ S[m + (k + k * m)]
                           ≡ S[(m + k) + k * m] by add_assoc m k (k * m)
                           ≡ S[(k + m) + k * m] by add_comm m k
                           ≡ S[k + (m + k * m)] by add_assoc k m (k * m)
                           ≡ S[k + n * m]
                           ≡ n + n * m
    }
  }

// Multiplication is commutative (detailed proof).
val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero → eqns 0 * m ≡ 0;
             eqns m * 0 ≡ 0 by mul_n_zero m;
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

val rec compare_refl : ∀n∈nat, compare n n ≡ Eq =
  fun n {
    case n {
      0    → qed
      S[m] → compare_refl m
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

val rec compare_sym : ∀n m∈nat, compare n m ≡ inverse (compare m n) =
  fun n m {
    case n {
      0     → case m {
        0     → qed
        S[m'] → qed
      }
      S[n'] → case m {
        0     → qed
        S[m'] → compare_sym n' m'
      }
    }
  }

val zero_leq : ∀b∈nat, 0 ≤ b =
  fun b {
    case b {
      0    → qed
      S[p] → qed
    }
  }

val rec succ_leq : ∀b1 b2∈nat, b1 ≤ b2 ⇒ b1 ≤ S[b2] =
  fun b1 b2 h {
    case b1 {
      0     → qed
      S[p1] →
        case b2 {
          0     → ✂
          S[p2] → use succ_leq p1 p2 h
        }
    }
  }

val rec leq_add : ∀a1 b1 a2 b2∈nat, a1 ≤ a2 ⇒ b1 ≤ b2 ⇒ a1 + b1 ≤ a2 + b2 =
  fun a1 b1 a2 b2 h1 h2 {
    case a1 {
      0     →
        case a2 {
          0     → qed
          S[p2] → show leq 0 p2 using zero_leq p2;
                  use leq_add a1 b1 p2 b2 {} h2;
                  use succ_leq b1 (p2 + b2) {}
        }
      S[p1] →
        case a2 {
          0     → ✂
          S[p2] → use leq_add p1 b1 p2 b2 h1 h2
        }
    }
  }

val rec leq_max_add : ∀a b∈nat, max a b ≤ a+b =
  fun a b {
    set auto 2 3;
    if leq a b {
      deduce max a b ≡ b;
      show b ≤ b using compare_refl b;
      deduce 0 ≤ a;
      use leq_add 0 b a b {} {};
      qed
    } else {
      deduce max a b ≡ a;
      show a ≤ a using compare_refl a;
      deduce 0 ≤ b;
      use leq_add a 0 a b {} {};
      use add_n_zero a;
      qed
    }
  }

val rec leq_trans : ∀a b c∈nat, a ≤ b ⇒ b ≤ c ⇒ a ≤ c =
  fun a b c h1 h2 {
    set auto 2 3;
    case a {
      0     → qed
      S[a1] →
        case b {
          0     → ✂
          S[b1] →
            case c {
              0     → ✂
              S[c1] → leq_trans a1 b1 c1 {} {}
            }
        }
    }
  }

val rec lt_trans : ∀a b c∈nat, a < b ⇒ b < c ⇒ a < c =
  fun a b c h1 h2 {
    set auto 2 3;
    case a {
      0     → qed
      S[a1] →
        case b {
          0     → ✂
          S[b1] →
            case c {
              0     → ✂
              S[c1] → lt_trans a1 b1 c1 {} {}
            }
        }
    }
  }

val rec geq_trans : ∀a b c∈nat, a ≥ b ⇒ b ≥ c ⇒ a ≥ c =
  fun a b c h1 h2 {
    set auto 2 3;
    case c {
      0     → qed
      S[c1] →
        case b {
          0     → ✂
          S[b1] →
            case a {
              0     → ✂
              S[a1] → geq_trans a1 b1 c1 {} {}
            }
        }
    }
  }

val rec gt_trans : ∀a b c∈nat, a > b ⇒ b > c ⇒ a > c =
  fun a b c h1 h2 {
    set auto 2 3;
    case c {
      0     → qed
      S[c1] →
        case b {
          0     → ✂
          S[b1] →
            case a {
              0     → ✂
              S[a1] → gt_trans a1 b1 c1 {} {}
            }
        }
    }
  }

val leq_geq : ∀a b∈nat, a ≤ b ≡ b ≥ a =
  fun a b { set auto 1 1; compare_sym a b }
val lt_gt   : ∀a b∈nat, a < b ≡ b > a =
  fun a b { set auto 1 1; compare_sym a b }

val leq_lt : ∀a b∈nat, a ≤ b ≡ not (b < a) =
  fun a b { set auto 2 2; compare_sym a b }
val geq_gt : ∀a b∈nat, a ≥ b ≡ not (b > a) =
  fun a b { set auto 2 2; compare_sym a b }

val leq_refl : ∀a∈nat, a ≤ a = fun a { compare_refl a }
val geq_refl : ∀a∈nat, a ≥ a = fun a { compare_refl a }

val leq_total : ∀a b∈nat, a ≤ b || b ≤ a =
  fun a b { set auto 2 2; compare_sym a b }
val geq_total : ∀a b∈nat, a ≥ b || b ≥ a =
  fun a b { set auto 2 2; compare_sym a b }

val leq_anti : ∀a b∈nat, a ≤ b ⇒ b ≤ a ⇒ a ≡ b =
  fun a b h1 h2 { set auto 2 2; compare_sym a b }
val geq_anti : ∀a b∈nat, a ≥ b ⇒ b ≥ a ⇒ a ≡ b =
  fun a b h1 h2 { set auto 2 2; compare_sym a b }

val rec div_mod : ∀n∈nat,∀m∈[S of nat], (n / m) * m + n % m ≡ n =
  fun n m {
    case sub_size n m {
      InL[r]  → qed
      InR[n'] →
        case n' {
          0      → use add_n_zero m; qed
          S[n''] → eqns n / m * m + n % m
                      ≡ S[n' / m] * m + n' % m
                      ≡ (m + n' / m * m) + n' % m
                      ≡ m + (n' / m * m + n' % m)
                         by add_assoc m (n' / m * m) (n' % m)
                      ≡ m + n' by div_mod n' m
                      ≡ n
        }
    }
  }
