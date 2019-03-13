type rec nat = [ Z ; S of nat ]

val rec id_nat : nat ⇒ nat =
  fun n {
    case n {
      Z    → Z
      S[p] → S[id_nat p]
    }
  }

val rec id_nat_id : ∀n∈nat, id_nat n ≡ n =
  fun m {
    case m {
      Z    → {}
      S[p] → let ind_hyp : id_nat p ≡ p = id_nat_id p; {}
    }
  }
