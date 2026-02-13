include lib.nat
include lib.nat_proofs

// We define the real McCarthy91 function as a term object.

def mccarthy91_hard : τ =
  fix mccarthy91 {
    fun n {
      if n > 100 {
        n - 10
      } else {
        mccarthy91 (mccarthy91 (n + 11))
      }
    }
  }

// It cannot be defined as a terminating function directly.

//val mccarthy91 : nat ⇒ nat =
//  mccarthy91_hard

// However, McCarthy91 has another, non-recursive definition!

val mccarthy91_easy : nat ⇒ nat =
  fun n {
    if n > 100 {
      n - 10
    } else {
      91
    }
  }

// We firt prove that the McCarthy91 function is equal to 91 bellow 100.

val hard_lemma : ∀n∈nat, n > 100 ≡ false ⇒ mccarthy91_hard n ≡ 91 =
  fun n eq { set auto 0 0;
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] →
    case n { 0 → qed | S[n] → ✂
    }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}

// We prove the equivalence between the two definitions.

val hard_is_easy : ∀n∈nat, mccarthy91_easy n ≡ mccarthy91_hard n =
  fun n {
    if n > 100 {
      deduce mccarthy91_easy n ≡ n - 10;
      deduce mccarthy91_hard n ≡ n - 10;
      qed
    } else {
      deduce mccarthy91_easy n ≡ 91;
      show mccarthy91_hard n ≡ 91 using hard_lemma n {};
      qed
    }
  }

// We can finally type the real McCarthy91 function.

val mccarthy91 : nat ⇒ nat =
  fun n {
    check { mccarthy91_easy n }  // Term used for type-checking.
      for { mccarthy91_hard n }  // Actual term used in the definition.
      because { hard_is_easy n } // Proof that they are equal.
    // The above really is "mccarthy91_hard n" (up to erasure).
  }


val ok : mccarthy91 ≡ fun n { mccarthy91_hard n } = {}
