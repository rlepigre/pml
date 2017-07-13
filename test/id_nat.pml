type rec nat = [ Z ; S of nat ]

val rec id_nat : nat ⇒ nat = fun n →
  case n {
    | Z[] → Z[]
    | S[p] → S[id_nat p]
  }
