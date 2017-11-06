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

// Hard version as a value object (not typed).
def mccarthy91_hard : ι = fix
  fun mccarthy91 n {
    if gt n u100 {
      minus n u10
    } else {
      mccarthy91 (mccarthy91 (add n u11))
    }
  }

// NOTE: we do not have [mccarthy91_easy ≡ mccarthy91_hard].

val hard_lemma : ∀n∈nat, gt n u100 ≡ false ⇒ mccarthy91_hard n ≡ u91 =
  fun n0 hyp {
    {- too_slow -}
//    let n = n0;
//    case n {        Z → {} // n₀ = 0
//    S[n] → case n { Z → {} // n₀ = 1
//    S[n] → case n { Z → {} // n₀ = 2
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 10
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 20
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 30
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 40
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 50
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 60
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 70
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 80
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 90
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {}
//    S[n] → case n { Z → {} // n₀ = 100
//    S[_] → ✂ }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
//    }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
  }

// Equiv
val hard_is_easy : ∀n∈nat, mccarthy91_easy n ≡ mccarthy91_hard n =
  fun n {
    use gt_total n u100;
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
