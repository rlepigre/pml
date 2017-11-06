include lib.nat
include lib.nat_proofs

// Easy version.
val mccarthy91_easy : nat ⇒ nat =
  fun n {
    if gt n u100 {
      minus n u10
    } else {
      u91
    }
  }

val rec mccarthy91_hard : nat ↝ nat =
  fun n {
    if gt n u100 {
      minus n u10
    } else {
      mccarthy91_hard (mccarthy91_hard (add n u11))
    }
  }

// NOTE: we do not have [mccarthy91_easy ≡ mccarthy91_hard].

val hard_lemma : ∀n∈nat, gt n u100 ≡ false ⇒ mccarthy91_hard n ≡ u91 =
  fun n hyp {
    {- takes_too_long -}
    //case n {        Zero → {} // n = 0
    //S[k] → case k { Zero → {} // n = 1
    //S[k] → case k { Zero → {} // n = 2
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 10
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 20
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 30
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 40
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 50
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 60
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 70
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 80
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 90
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {}
    //S[k] → case k { Zero → {} // n = 100
    //S[_] → ✂ }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
    //}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
  }

// Equiv
val hard_is_easy : ∀n∈nat, mccarthy91_easy n ≡ mccarthy91_hard n =
  fun n {
    if gt n u100 { // n > 100
      deduce mccarthy91_easy n ≡ minus n u10;
      deduce mccarthy91_hard n ≡ minus n u10;
      qed
    } else { // n ≤ 100
      deduce mccarthy91_easy n ≡ u91;
      show mccarthy91_hard n ≡ u91 using hard_lemma n {};
      qed
    }
  }

// Real function.
val mccarthy91 : nat ⇒ nat =
  fun n {
    check mccarthy91_easy n for mccarthy91_hard n
      because hard_is_easy n
  }
