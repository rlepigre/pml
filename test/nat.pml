
def nat : ο = μx [ Z of {} ; S of x ]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

val id_nat : nat ⇒ nat = fix fun id_nat n →
  case n of
  | Z[u] → zero
  | S[p] → succ (id_nat p)
