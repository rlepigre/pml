include lib.nat
include lib.nat_proofs

// Let's give names to relevant unary numbers.

val u0   : nat = zero
val u1   : nat = succ u0
val u2   : nat = succ u1
val u3   : nat = succ u2
val u4   : nat = succ u3
val u5   : nat = succ u4
val u6   : nat = succ u5
val u7   : nat = succ u6
val u8   : nat = succ u7
val u9   : nat = succ u8
val u10  : nat = succ u9
val u11  : nat = succ u10
val u90  : nat = mul u9 u10
val u91  : nat = succ u90
val u100 : nat = mul u10 u10
val u101 : nat = succ u100





// We define the real McCarthy91 function as a term object.

def mccarthy91_hard : τ =
  fix mccarthy91 {
    fun n {
      if n > u100 {
        n - u10
      } else {
        mccarthy91 (mccarthy91 (n + u11))
      }
    }
  }

// It cannot be defined as a terminating function directly.

//val mccarthy91 : nat ⇒ nat =
//  mccarthy91_hard





// However, McCarthy91 as another, non-recursive definition!

val mccarthy91_easy : nat ⇒ nat =
  fun n {
    if n > u100 {
      n - u10
    } else {
      u91
    }
  }





// We firt prove that the McCarthy91 function is equal to 91 bellow 100.

//val hard_lemma : ∀n∈nat, n > u100 ≡ false ⇒ mccarthy91_hard n ≡ u91 =
//  fun n eq {
//    case n { Zero → {} | S[n] →
//    case n { Zero → {} | S[n] →
//    case n { Zero → {} | S[n] →
//    case n { Zero → {} | S[n] →
//    case n { Zero → {} | S[n] →
//      {- and_95_more_lines -}
//      // At some point, we get a contradiction and use scissors ✂.
//    }}}}}
//  }

val hard_lemma : ∀n∈nat, n > u100 ≡ false ⇒ mccarthy91_hard n ≡ u91 =
  fun n eq {
    //{- takes too long -}
    set auto 101 1; {}
  }





// We prove the equivalence between the two definitions.

val hard_is_easy : ∀n∈nat, mccarthy91_easy n ≡ mccarthy91_hard n =
  fun n {
    if n > u100 {
      deduce mccarthy91_easy n ≡ n - u10;
      deduce mccarthy91_hard n ≡ n - u10;
      qed
    } else {
      deduce mccarthy91_easy n ≡ u91;
      show mccarthy91_hard n ≡ u91 using hard_lemma n {};
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
