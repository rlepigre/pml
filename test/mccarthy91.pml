include lib.nat
include lib.nat_proofs

// Hard version as a non terminating function.
val rec mccarthy91 : nat ↝ nat =
  fun n {
    if gt n 100 {
      minus n 10
    } else {
      mccarthy91 (mccarthy91 (add n 11))
    }
  }

// Easy version.
val mccarthy91_easy : nat ⇒ nat =
  fun n {
    if gt n 100 {
      minus n 10
    } else {
      91
    }
  }


// NOTE: we do not have [mccarthy91_easy ≡ mccarthy91].

//val test : mccarthy91 0 ≡ 91 = {}

val hard_lemma : ∀n∈nat, gt n 100 ≡ false ⇒ mccarthy91 n ≡ 91 =
  fun n hyp {
    //set auto 101 1; {}
    {- takes_too_long -}
  }

// Equiv
val hard_is_easy : ∀n∈nat, mccarthy91_easy n ≡ mccarthy91 n =
  fun n {
    if gt n 100 { // n > 100
      deduce mccarthy91_easy n ≡ minus n 10;
      deduce mccarthy91 n ≡ minus n 10;
      qed
    } else { // n ≤ 100
      deduce mccarthy91_easy n ≡ 91;
      show mccarthy91 n ≡ 91 using hard_lemma n {};
      qed
    }
  }

// Real function.
val mccarthy91 : nat ⇒ nat =
  fun n {
      check { mccarthy91_easy n }
      for { mccarthy91 n }
      because { hard_is_easy n }
  }
