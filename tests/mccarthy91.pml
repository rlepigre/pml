include lib.nat
include lib.nat_proofs

// Hard version as a non terminating function.
val rec mccarthy91 : nat ↛ nat =
  fun n {
    if n > 100 {
      n - 10
    } else {
      mccarthy91 (mccarthy91 (n + 11))
    }
  }

// Easy version.
val mccarthy91_easy : nat ⇒ nat =
  fun n {
    if n > 100 {
      n - 10
    } else {
      91
    }
  }


// NOTE: we do not have [mccarthy91_easy ≡ mccarthy91].

//val test : mccarthy91 0 ≡ 91 = {}

val hard_lemma : ∀n∈nat, n ≤ 100 ⇒ mccarthy91 n ≡ 91 =
  fun n hyp {
    //set auto 101 1;
    {-qed-} // takes_too_long
  }

// Equiv
val hard_is_easy : ∀n∈nat, mccarthy91_easy n ≡ mccarthy91 n =
  fun n {
    if n > 100 { // n > 100
      deduce mccarthy91_easy n ≡ n - 10;
      deduce mccarthy91 n ≡ n - 10;
      qed
    } else { // n ≤ 100
      deduce n ≤ 100 using { geq_gt 100 n; leq_geq n 100};
      deduce mccarthy91_easy n ≡ 91;
      show mccarthy91 n ≡ 91 using hard_lemma n {};
      qed
    }
  }

// Real function.
val mccarthy91 : nat ⇒ nat =
  fun n {
      check mccarthy91_easy n for mccarthy91 n by hard_is_easy n
  }
