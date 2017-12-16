include lib.nat

type rec natbin = [ Zero of ∃n:ι, n∈(natbin | n ≠ End) ; One of natbin ; End ]

type nonzero = ∃n:ι, n∈(natbin | n ≠ End)

val zero_b : natbin = End

val rec succ_b : natbin ⇒ nonzero = fun n {
  case n {
    End     → One[End]
    Zero[p] → One[p]
    One[p]  → Zero[succ_b p]
  }
}

val rec nat_to_natbin : nat ⇒ natbin = fun n {
  case n {
    Zero → zero_b
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