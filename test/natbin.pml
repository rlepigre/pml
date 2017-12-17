include lib.nat

type rec natbin = [ Zero of {n∈natbin | n ≠ End} ; One of natbin ; End ]

type nonzero = {n∈natbin | n ≠ End}

val b0     : natbin  = End
val b1     : nonzero = One[End]

val rec succ_b : natbin ⇒ nonzero = fun n {
  case n {
    End     → b1
    Zero[p] → One[p]
    One[p]  → Zero[succ_b p]
  }
}

val rec pred_b : nonzero ⇒ natbin = fun n {
  case n {
    End     → ✂
    Zero[p] → One[pred_b p]
    One[p]  → case p {
      End     → End
      Zero[_] → Zero[p]
      One[_]  → Zero[p]
    }
  }
}

val rec pred_succ : ∀n∈natbin, pred_b (succ_b n) ≡ n =
  take n;
  case n {
    End     → qed
    Zero[p] → set auto 1 0; qed
    One[p]  → use pred_succ p; qed
  }

val rec nat_to_natbin : nat ⇒ natbin = fun n {
  case n {
    Zero → b0
    S[p] → succ_b (nat_to_natbin p)
  }
}

val rec natbin_to_nat : natbin ⇒ nat = fun n {
   case n {
     End     → zero
     Zero[p] → mul (natbin_to_nat p) u2
     One[p]  → succ (mul (natbin_to_nat p) u2)
   }
}

val rec lemma1 : ∀n∈natbin, natbin_to_nat (succ_b n) ≡ succ (natbin_to_nat n) =
  take n;
  case n {
    End     → qed
    Zero[p] → qed
    One[p]  → show natbin_to_nat (succ_b p) ≡ succ (natbin_to_nat p) using lemma1 p;
              deduce natbin_to_nat (succ_b n) ≡ mul (succ (natbin_to_nat p)) u2;
              deduce succ (natbin_to_nat n)   ≡ succ (succ (mul (natbin_to_nat p) u2));
              qed
  }

val rec bij1 : ∀n∈nat, natbin_to_nat (nat_to_natbin n) ≡ n =
  take n;
  case n {
    Zero → qed
    S[p] → show natbin_to_nat (nat_to_natbin p) ≡ p using bij1 p;
           use lemma1 (nat_to_natbin p);
           qed
  }

val double : natbin ⇒ natbin = fun n {
  case n {
    End     → End
    Zero[p] → Zero[Zero[p]]
    One[p]  → Zero[One[p]]
  }
}

val rec lemma2b : ∀n∈natbin,  double (succ_b n) ≡ succ_b (succ_b (double n)) =
  take n;
  case n {
    End     → qed
    Zero[p] → use lemma2b p; qed
    One[p]  → use lemma2b p; qed
  }

val rec lemma2 : ∀n∈nat, nat_to_natbin (mul n u2) ≡ double(nat_to_natbin n) =
  take n;
  case n {
    Zero → qed
    S[p] → deduce nat_to_natbin (mul n u2) ≡ nat_to_natbin (succ (succ (mul p u2)));
           deduce nat_to_natbin (mul n u2) ≡ succ_b (succ_b (nat_to_natbin (mul p u2)));
           show nat_to_natbin (mul n u2) ≡ succ_b (succ_b (double (nat_to_natbin p)))
             using lemma2 p;
           deduce double(nat_to_natbin n) ≡ double (succ_b (nat_to_natbin p));
           use lemma2b (nat_to_natbin p);
           qed
  }

val rec lemma3 : ∀n∈nonzero, natbin_to_nat n ≠ Zero =
  take n;
  case n {
    End     → ✂
    Zero[p] → deduce natbin_to_nat n ≡ mul (natbin_to_nat p) u2;
              use lemma3 p;
              case natbin_to_nat p {
                Zero → ✂
                S[q] → deduce natbin_to_nat n ≡ S[S[mul q u2]];
                       qed
              }
    One[p] → deduce natbin_to_nat n ≡ succ (mul (natbin_to_nat p) u2);
             qed
  }

val rec bij2 : ∀n∈natbin, nat_to_natbin (natbin_to_nat n) ≡ n =
  take n;
  case n {
    End     → qed
    Zero[p] → deduce natbin_to_nat n ≡ mul (natbin_to_nat p) u2;
              use lemma2 (natbin_to_nat p);
              use bij2 p;
              use lemma3 p;
              set auto 1 2;
              qed
    One[p]  → deduce natbin_to_nat n ≡ succ (mul (natbin_to_nat p) u2);
              use lemma2 (natbin_to_nat p);
              use bij2 p;
              set auto 1 2;
              qed
  }

type carry = [ Zero ; One ]

val rec add_aux : carry ⇒ natbin ⇒ natbin ⇒ natbin =
  fun carry n m {
    case carry {
      Zero →
        case n {
          End     → m
          Zero[p] →
            case m {
              End     → n
              Zero[q] → double(add_aux Zero p q)
              One[q]  → One [add_aux Zero p q]
            }
          One[p]  →
            case m {
              End     → n
              Zero[q] → One [add_aux Zero p q]
              One[q]  → double(add_aux One  p q)
            }
        }
      One  →
        case n {
          End     → succ_b m
          Zero[p] →
            case m {
              End     → succ_b n
              Zero[q] → One [add_aux Zero p q]
              One[q]  → double(add_aux One  p q)
            }
          One[p]  →
            case m {
              End     → succ_b n
              Zero[q] → double(add_aux One  p q)
              One[q]  → One [add_aux One  p q]
            }
        }
    }
  }

val rec add : natbin ⇒ natbin ⇒ natbin = fun n m { add_aux Zero n m }

val rec mul : natbin ⇒ natbin ⇒ natbin = fun n m {
  case n {
    End     → End
    Zero[p] → double (mul p m)
    One[p]  → add m (double (mul p m))
  }
}

//// Number constants ////////////////////////////////////////////////////////

val b2   : nonzero = succ_b b1
val b3   : nonzero = succ_b b2
val b4   : nonzero = succ_b b3
val b5   : nonzero = succ_b b4
val b6   : nonzero = succ_b b5
val b7   : nonzero = succ_b b6
val b8   : nonzero = succ_b b7
val b9   : nonzero = succ_b b8
val b10  : nonzero = succ_b b9
val b11  : nonzero = succ_b b10
val b90  : nonzero = mul b10 b9
val b91  : nonzero = succ_b b90
val b100 : nonzero = mul b10 b10
val b101 : nonzero = succ_b b100
val b1000 : nonzero = mul b10 b100

// Print a natural number.
val rec print_nat : natbin ⇒ {} =
  fun n {
    case n {
      End     → {}
      Zero[p] → print_nat p; print "0"
      One[p]  → print_nat p; print "1"
    }
  }

// Print a natural number with a newline.
val println_nat : natbin ⇒ {} =
  fun n { print_nat n; print "\n" }

val rec fact2 : natbin ↝ natbin  = fun n {
  case n {
    End     → b1
    Zero[_] → mul n (fact2 (pred_b n))
    One[_]  → mul n (fact2 (pred_b n))
  }
}

val rec fact1 : ∀m∈nat, ∀n∈(natbin | n ≡ nat_to_natbin m), (fact2 n)∈natbin = fun m n {
  case n {
    End     → b1
    Zero[_] →
      case m {
        Zero → ✂
        S[q] → deduce n ≡ succ_b (nat_to_natbin q);
               let p = pred_b n;
               show p ≡ nat_to_natbin q using pred_succ (nat_to_natbin q);
               let r = fact1 q p;
               let r2 = mul n r;
               deduce r ≡ fact2 p;
               deduce r2 ≡ fact2 n;
               r2
      }
    One[_] →
      case m {
        Zero → ✂
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

val rec fact : natbin → natbin = fun n {
  check use bij2 n; fact1 (natbin_to_nat n) n for fact2 n
}

val test1 : ∀n∈natbin, fact n ≡ fact2 n = fun n { qed }

val test2 : {} = print "fact(10) = "; println_nat (fact b10)
