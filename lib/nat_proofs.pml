// Proofs on unary natural numbers.

include lib.nat
include lib.bool

//// Properties of addition //////////////////////////////////////////////////

// Associativity of addition (detailed proof).
val rec add_assoc : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  take m n p;
  case m {
    Zero → show 0 + (n + p)
             ≡ n + p
             ≡ (0 + n) + p
    S[k] → show m + (n + p)
             ≡ S[k] + (n + p)
             ≡ S[k + (n + p)]
             ≡ S[(k + n) + p] by add_assoc k n p
             ≡ S[k + n] + p;
           show (m + n) + p
             ≡ (S[k] + n) + p
             ≡ S[k + n] + p;
           qed
  }

// Associativity of addition (shortest proof).
val rec add_assoc2 : ∀m n p∈nat, m + (n + p) ≡ (m + n) + p =
  take m n p;
  case m {
    Zero → qed
    S[k] → add_assoc2 k n p
  }

// Zero as a neutral element on the right (detailed proof).
val rec add_n_zero : ∀n∈nat, n + 0 ≡ n =
  take n;
  case n {
    Zero → qed
    S[k] → show n + 0 ≡ S[k] + 0 ≡ S[k + 0]
             ≡ S[k] by add_n_zero k ≡ n
  }

// Successor on the right can be taken out (detailed proof).
val rec add_n_succ : ∀m n∈nat, m + S[n] ≡ S[m + n] =
  take m n;
  case m {
    Zero → qed
    S[k] → show m + S[n] ≡ S[k + S[n]]
           ≡ S[S[k + n]] by add_n_succ k n
           ≡ S[m + n]
  }

// Commutativity of addition (detailed proof).
val rec add_comm : ∀m n∈nat, m + n ≡ n + m =
  take m n;
  case m {
    Zero → show 0 + n ≡ n ≡ n + 0 by add_n_zero n
    S[k] → show m + n ≡ S[k + n]
             ≡ S[n + k]    by add_comm k n
             ≡ n + m       by add_n_succ n k
  }

//// Properties of multiplication ////////////////////////////////////////////

// Zero as an absorbing element on the right (detailed proof).
val rec mul_n_zero : ∀n∈nat, n * 0 ≡ 0 =
  take n;
  case n {
    Zero → show 0 * 0 ≡ 0
    S[k] → show S[k] * 0 ≡ 0 + k * 0
             ≡ 0 + 0 by mul_n_zero k
             ≡ 0
  }

val rec mul_neutral : ∀n∈nat, 1 * n ≡ n =
  take n; add_n_zero n

// Successor on the right can be taken out (detailed proof).
val rec mul_n_succ : ∀n m∈nat, n * S[m] ≡ n + n * m =
  take n m;

  case n {
    Zero → show 0 * S[m] ≡ 0 + 0 * m ≡ 0
    S[k] → show n * S[m] ≡ S[m] + k * S[m]
             ≡ S[m] + (k + k * m) by mul_n_succ k m
             ≡ S[m + (k + k * m)]
             ≡ S[(m + k) + k * m] by add_assoc m k (k * m)
             ≡ S[(k + m) + k * m] by add_comm m k
             ≡ S[k + (m + k * m)] by add_assoc k m (k * m)
             ≡ S[k + n * m]
             ≡ n + n * m
  }

// Multiplication is commutative (detailed proof).
val rec mul_comm : ∀n m∈nat, n * m ≡ m * n =
  take n m;
  case n {
    Zero → show 0 * m ≡ 0 ≡ m * 0 by mul_n_zero m
    S[k] → show m + k * m ≡ m + m * k using mul_comm k m
           ≡ m * n by mul_n_succ m k
  }

// Left distributivity of multiplication over addition (detailed proof).
val rec mul_dist_l : ∀m n p∈nat, m * (n + p) ≡ m * n + m * p =
  take m n p;
  case m {
    Zero → show 0 * (n + p) ≡ 0 ≡ 0 * n + 0 * p
    S[k] → show m * (n + p) ≡ (n + p) + k * (n + p)
           ≡ (n + p) + (k * n + k * p) by mul_dist_l k n p
           ≡ n + (p + (k * n + k * p)) by add_assoc n p (k * n + k * p)
           ≡ n + ((p + k * n) + k * p) by add_assoc p (k * n) (k * p)
           ≡ n + ((k * n + p) + k * p) by add_comm p (k * n)
           ≡ n + (k * n + (p + k * p)) by add_assoc (k * n) p (k * p)
           ≡ (n + k * n) + (p + k * p) by add_assoc n (k * n) (p + k * p)
           ≡ m * n + m * p
  }

// Right distributivity of multiplication over addition (detailed proof).
val rec mul_dist_r : ∀m n p∈nat, (m + n) * p ≡ m * p + n * p =
  take m n p;
  show (m + n) * p ≡ p * (m + n) by mul_comm (m+n) p
    ≡ p * m + p * n by mul_dist_l p m n
    ≡ m * p + n * p by {mul_comm m p; mul_comm n p}

// Associativity of multiplication (detailed proof).
val rec mul_assoc : ∀m n p∈nat, m * (n * p) ≡ (m * n) * p =
  take m n p;
  case m {
    Zero → show 0 * (n * p) ≡ 0 ≡ (0 * n) * p
    S[k] → show m * (n * p) ≡ n * p + k * (n * p)
           ≡ n * p + (k * n) * p by mul_assoc k n p
           ≡ (n + k * n) * p by mul_dist_r n (k * n) p
           ≡ (m * n) * p
  }

// one if left neutral for mul
val mul_one_n : ∀m∈nat, 1 * m ≡ m =
  take m;
  show 1 * m ≡ m + 0 * m ≡ m + 0 ≡ m by add_n_zero m

// one is right neutral too
val mul_n_one : ∀m∈nat, m * 1 ≡ m =
  take m; mul_one_n m; mul_comm 1 m

// results about comparison
include lib.comparison

val rec succ_gr : ∀n m∈nat, compare n m ≡ Gr ⇒ compare S[n] m ≡ Gr =
  take n m; suppose compare n m ≡ Gr;
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

val rec succ_ls : ∀n m∈nat, compare n m ≡ Ls ⇒ compare n S[m] ≡ Ls =
  take n m; suppose compare n m ≡ Ls;
  case n {
    Zero → {}
    S[k] →
      case m {
        Zero → ✂
        S[l] → deduce compare k l ≡ Ls;
               use succ_ls k l {}; qed
      }
  }

val rec succ_eq_r : ∀n m∈nat, compare n m ≡ Eq ⇒ compare n S[m] ≡ Ls =
  take n m; suppose compare n m ≡ Eq;
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

val rec succ_eq_l : ∀n m∈nat, compare n m ≡ Eq ⇒ compare S[n] m ≡ Gr =
  take n m; suppose compare n m ≡ Eq;
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
               use succ_eq_l k l {}; qed
      }
  }

val rec compare_refl : ∀n∈nat, compare n n ≡ Eq =
  take n;
  case n {
    0    → qed
    S[m] → compare_refl m
  }

val rec compare_eq : ∀n m∈nat, compare n m ≡ Eq ⇒ n ≡ m =
  take n m; suppose compare n m ≡ Eq;
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

val rec compare_sym : ∀n m∈nat, compare n m ≡ inverse (compare m n) =
  take n m;
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

// ordering

// zero is minimal
val zero_leq : ∀b∈nat, 0 ≤ b =
  take b; set auto 1 3; qed

// leq and succ
val rec succ_leq : ∀b1 b2∈nat, b1 ≤ b2 ⇒ b1 ≤ S[b2] =
  take b1 b2; suppose b1 ≤ b2;
  case compare b1 b2 {
    Ls → succ_ls b1 b2 {}
    Eq → succ_eq_r b1 b2 {}
    Gr → ✂
  }

// ordering axioms
val leq_refl : ∀a∈nat, a ≤ a = fun a { compare_refl a }
val geq_refl : ∀a∈nat, a ≥ a = fun a { compare_refl a }

val leq_geq : ∀a b∈nat, a ≤ b ≡ b ≥ a =
  fun a b { set auto 1 1; compare_sym a b }
val lt_gt   : ∀a b∈nat, a < b ≡ b > a =
  fun a b { set auto 1 1; compare_sym a b }

val leq_lt : ∀a b∈nat, a ≤ b ≡ not (b < a) =
  fun a b { set auto 2 2; compare_sym a b }
val geq_gt : ∀a b∈nat, a ≥ b ≡ not (b > a) =
  fun a b { set auto 2 2; compare_sym a b }

val rec leq_trans : ∀a b c∈nat, a ≤ b ⇒ b ≤ c ⇒ a ≤ c =
  take a b c; suppose a ≤ b, b ≤ c;
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

val rec lt_trans : ∀a b c∈nat, a < b ⇒ b < c ⇒ a < c =
  take a b c; suppose a < b, b < c;
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

val rec geq_trans : ∀a b c∈nat, a ≥ b ⇒ b ≥ c ⇒ a ≥ c =
  take a b c; suppose a ≥ b, b ≥ c;
  deduce b ≤ a by leq_geq b a;
  deduce c ≤ b by leq_geq c b;
  showing c ≤ a by leq_geq c a;
  leq_trans c b a {} {}

val rec gt_trans : ∀a b c∈nat, a > b ⇒ b > c ⇒ a > c =
  take a b c; suppose a > b; suppose b > c;
  lt_gt b a; lt_gt c b; lt_gt c a; lt_trans c b a {} {}

val leq_total : ∀a b∈nat, a ≤ b || b ≤ a =
  take a b; set auto 2 2; compare_sym a b
val geq_total : ∀a b∈nat, a ≥ b || b ≥ a =
  take a b; set auto 2 2; compare_sym a b

val leq_anti : ∀a b∈nat, a ≤ b ⇒ b ≤ a ⇒ a ≡ b =
  take a b; suppose a ≤ b, b ≤ a; set auto 2 2; compare_sym a b
val geq_anti : ∀a b∈nat, a ≥ b ⇒ b ≥ a ⇒ a ≡ b =
  take a b; suppose a ≥ b, b ≥ a; set auto 2 2; compare_sym a b

// addition is increasing
val rec leq_add : ∀a1 b1 a2 b2∈nat, a1 ≤ a2 ⇒ b1 ≤ b2 ⇒ a1 + b1 ≤ a2 + b2 =
  take a1 b1 a2 b2; suppose a1 ≤ a2; suppose b1 ≤ b2;
  case a1 {
    0     →
      case a2 {
        0     → qed
        S[p2] → show leq 0 p2 using zero_leq p2;
                use leq_add a1 b1 p2 b2 {} {};
                use succ_leq b1 (p2 + b2) {}
      }
    S[p1] →
      case a2 {
        0     → ✂
        S[p2] → use leq_add p1 b1 p2 b2 {} {}
      }
  }

// multiplication is increasing
val rec leq_mul : ∀a1 b1 a2 b2∈nat, a1 ≤ a2 ⇒ b1 ≤ b2 ⇒ a1 * b1 ≤ a2 * b2 =
  take a1 b1 a2 b2; suppose a1 ≤ a2; suppose b1 ≤ b2;
  case a1 {
    0     → zero_leq (a2 * b2)
    S[p1] →
      case a2 {
        0     → ✂
        S[p2] → showing b1 + p1 * b1 ≤ b2 + p2 * b2;
                deduce p1 ≤ p2 ≡ a1 ≤ a2;
                use leq_mul p1 b1 p2 b2 {} {};
                use leq_add b1 (p1 * b1) b2 (p2 * b2) {} {}
      }
  }

// max is smaller than sum
val rec leq_max_add : ∀a b∈nat, max a b ≤ a+b =
  take a b;
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

// correction of division and modulo
val rec div_mod : ∀n∈nat,∀m∈[S of nat], (n / m) * m + n % m ≡ n =
  take n m;
  case sub_size n m {
    InL[r]  → qed
    InR[n'] →
      case n' {
        0      → use add_n_zero m; qed
        S[n''] → show n / m * m + n % m
                 ≡ S[n' / m] * m + n' % m
                 ≡ (m + n' / m * m) + n' % m
                 ≡ m + (n' / m * m + n' % m)
                   by add_assoc m (n' / m * m) (n' % m)
                 ≡ m + n' by div_mod n' m
                 ≡ n
      }
  }
