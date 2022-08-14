include lib.nat

type rec natbin = [ B0 of {n∈natbin | n ≠ Zero} ; B1 of natbin ; Zero ]

type nonzero = {n∈natbin | n ≠ Zero}

val b0 : natbin  = Zero
val b1 : nonzero = B1[Zero]

val rec succ_b : natbin ⇒ nonzero = fun n {
  case n {
    0     → b1
    B0[p] → B1[p]
    B1[p] → B0[succ_b p]
  }
}

val rec pred_b : nonzero ⇒ natbin = fun n {
  case n {
    0     → ✂
    B0[p] → B1[pred_b p]
    B1[p] → case p {
      0     → Zero
      B0[_] → B0[p]
      B1[_] → B0[p]
    }
  }
}

val rec pred_succ : ∀n∈natbin, pred_b (succ_b n) ≡ n =
  take n;
  case n {
    0     → qed
    B0[p] → set auto 1 0; qed
    B1[p] → use pred_succ p; qed
  }

val rec nat_to_natbin : nat ⇒ natbin = fun n {
  case n {
    0    → b0
    S[p] → succ_b (nat_to_natbin p)
  }
}

val rec natbin_to_nat : natbin ⇒ nat = fun n {
   case n {
     0     → zero
     B0[p] → mul (natbin_to_nat p) 2
     B1[p] → succ (mul (natbin_to_nat p) 2)
   }
}

val rec lemma1 : ∀n∈natbin, natbin_to_nat (succ_b n) ≡ succ (natbin_to_nat n) =
  take n;
  case n {
    0     → qed
    B0[p] → qed
    B1[p] → show natbin_to_nat (succ_b p) ≡ succ (natbin_to_nat p) using lemma1 p;
            deduce natbin_to_nat (succ_b n) ≡ mul (succ (natbin_to_nat p)) 2;
            deduce succ (natbin_to_nat n)   ≡ succ (succ (mul (natbin_to_nat p) 2));
            qed
  }

val rec bij1 : ∀n∈nat, natbin_to_nat (nat_to_natbin n) ≡ n =
  take n;
  case n {
    0    → qed
    S[p] → show natbin_to_nat (nat_to_natbin p) ≡ p using bij1 p;
           use lemma1 (nat_to_natbin p);
           qed
  }

val double : natbin ⇒ natbin = fun n {
  case n {
    0     → Zero
    B0[p] → B0[B0[p]]
    B1[p]  → B0[B1[p]]
  }
}

val rec lemma2b : ∀n∈natbin,  double (succ_b n) ≡ succ_b (succ_b (double n)) =
  take n;
  case n {
    0     → qed
    B0[p] → use lemma2b p; qed
    B1[p] → use lemma2b p; qed
  }

val rec lemma2 : ∀n∈nat, nat_to_natbin (mul n 2) ≡ double(nat_to_natbin n) =
  take n;
  case n {
    0    → qed
    S[p] → deduce nat_to_natbin (mul n 2) ≡ nat_to_natbin (succ (succ (mul p 2)));
           deduce nat_to_natbin (mul n 2) ≡ succ_b (succ_b (nat_to_natbin (mul p 2)));
           show nat_to_natbin (mul n 2) ≡ succ_b (succ_b (double (nat_to_natbin p)))
             using lemma2 p;
           deduce double(nat_to_natbin n) ≡ double (succ_b (nat_to_natbin p));
           use lemma2b (nat_to_natbin p);
           qed
  }

val rec lemma3 : ∀n∈nonzero, natbin_to_nat n ≠ Zero =
  take n;
  case n {
    0     → ✂
    B0[p] → deduce natbin_to_nat n ≡ mul (natbin_to_nat p) 2;
              use lemma3 p;
              case natbin_to_nat p {
                0 → ✂
                S[q] → deduce natbin_to_nat n ≡ S[S[mul q 2]];
                       qed
              }
    B1[p] → deduce natbin_to_nat n ≡ succ (mul (natbin_to_nat p) 2);
             qed
  }

val rec bij2 : ∀n∈natbin, nat_to_natbin (natbin_to_nat n) ≡ n =
  take n;
  case n {
    0     → qed
    B0[p] → deduce natbin_to_nat n ≡ mul (natbin_to_nat p) 2;
              use lemma2 (natbin_to_nat p);
              use bij2 p;
              use lemma3 p;
              set auto 1 1;
              qed
    B1[p]  → deduce natbin_to_nat n ≡ succ (mul (natbin_to_nat p) 2);
              use lemma2 (natbin_to_nat p);
              use bij2 p;
              set auto 1 1;
              qed
  }

type carry = [ Zero ; One ]

val rec add_aux : carry ⇒ natbin ⇒ natbin ⇒ natbin =
  fun carry n m {
    case carry {
      0    →
        case n {
          0     → m
          B0[p] →
            case m {
              0     → n
              B0[q] → double(add_aux Zero p q)
              B1[q] → B1[add_aux Zero p q]
            }
          B1[p]  →
            case m {
              0     → n
              B0[q] → B1[add_aux Zero p q]
              B1[q] → double(add_aux One  p q)
            }
        }
      One  →
        case n {
          0     → succ_b m
          B0[p] →
            case m {
              0     → succ_b n
              B0[q] → B1[add_aux Zero p q]
              B1[q] → double(add_aux One  p q)
            }
          B1[p] →
            case m {
              0  → succ_b n
              B0[q] → double(add_aux One  p q)
              B1[q] → B1[add_aux One  p q]
            }
        }
    }
  }

val rec add : natbin ⇒ natbin ⇒ natbin = fun n m { add_aux Zero n m }

val rec mul : natbin ⇒ natbin ⇒ natbin = fun n m {
  case n {
    0     → Zero
    B0[p] → double (mul p m)
    B1[p] → add m (double (mul p m))
  }
}

// From now on, numerical constant are natbin
val zero : natbin = b0
val succ : natbin ⇒ natbin = succ_b
val dble : natbin ⇒ natbin = double

// Print a natural number.
val rec print_nat : natbin ⇒ {} =
  fun n {
    case n {
      0     → {}
      B0[p] → print_nat p; print "0"
      B1[p] → print_nat p; print "1"
    }
  }

// Print a natural number with a newline.
val println_nat : natbin ⇒ {} =
  fun n { print_nat n; print "\n" }

val rec fact2 : natbin ⇏ natbin  = fun n {
  case n {
    0     → b1
    B0[_] → mul n (fact2 (pred_b n))
    B1[_] → mul n (fact2 (pred_b n))
  }
}

val rec fact1 : ∀m∈nat, ∀n∈(natbin | n ≡ nat_to_natbin m), (fact2 n)∈natbin = fun m n {
  case n {
    0     → b1
    B0[_] →
      case m {
        0    → ✂
        S[q] → deduce n ≡ succ_b (nat_to_natbin q);
               let p = pred_b n;
               show p ≡ nat_to_natbin q using pred_succ (nat_to_natbin q);
               let r = fact1 q p;
               let r2 = mul n r;
               deduce r ≡ fact2 p;
               deduce r2 ≡ fact2 n;
               r2
      }
    B1[_] →
      case m {
        0    → ✂
        S[q] → deduce n ≡ succ_b (nat_to_natbin q);
               let p = pred_b n;
               show p ≡ nat_to_natbin q using pred_succ (nat_to_natbin q);
               let r = fact1 q p;
               let r2 = mul n r;
               deduce r ≡ fact2 p;
               deduce r2 ≡ fact2 n;
               r2
      }
  }
}

val fact : natbin ⇒ natbin = fun n {
    check { use bij2 n; fact1 (natbin_to_nat n) n }
    for { fact2 n }
}

val test1 : ∀n∈natbin, fact n ≡ fact2 n = fun n { qed }

val test2 : {} = print "fact(10) = "; println_nat (fact 10)
