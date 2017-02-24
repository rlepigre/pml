def nat : ο = μx [ Z of {} ; S of x ]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]
val one  : nat = succ zero
val two  : nat = succ one

val id_nat : nat ⇒ nat = fix fun id_nat n →
  case n of
  | Z[u] → Z[u]
  | S[p] → succ (id_nat p)

val test : nat = id_nat two

//val id_nat_id : ∀n:ι, n∈nat ⇒ id_nat n ≡ n = fix fun id_nat_id x →
//  case x of
//  | Z[u] → {}
//  | S[p] → let lem = id_nat_id p in {}
