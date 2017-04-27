type rec nat = [ Z ; S of nat ]

val zero : nat = Z[]
val succ : nat ⇒ nat = fun n → S[n]

val rec id_nat : nat ⇒ nat = fun n →
  case n {
    | Z[] → zero
    | S[p] → succ (id_nat p)
  }
