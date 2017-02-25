def nat : ο = μx [ Z of {} ∈ {} ; S of x ]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]
val one  : nat = succ zero
val two  : nat = succ one

val id_nat : nat ⇒ nat = fix fun id_nat n →
  case n of
  | Z[u] → Z[{}]
  | S[p] → succ (id_nat p)

val test : nat = id_nat two

val id_nat_id : ∀n:ι, n∈nat ⇒ id_nat n ≡ n = fix fun id_nat_id m →
  case m of
  | Z[u] → {}
  | S[p] → let lem = id_nat_id p in {}

val add : nat ⇒ nat ⇒ nat = fix fun add n m →
  case n of
  | Z[u] → m
  | S[p] → succ (add p m)

//val add_total :  ∀n:ι, ∀m:ι, n∈nat ⇒ m∈nat ⇒ ∃v:ι, add n m ≡ v = fix fun add_total n m →
//  case n of
//  | Z[u] → {}
//  | S[p] → let ind_hyp = add_total p m in {}

//val add_zero : ∀n:ι, n∈nat ⇒ add n zero ≡ n = fix fun add_zero n →
//  case n of
//  | Z[u] → {}
//  | S[p] → let ind_hyp : add p zero ≡ p = add_zero p in {}

val add_zero : ∀n:ι, n∈nat ⇒ add n zero ≡ n = fix fun add_zero n →
  case n of
  | Z[u] → {}
  | S[p] → let ind_hyp = add_zero p in {}

//val add_succ : ∀n:ι, ∀m:ι, n∈nat ⇒ m∈nat ⇒ add n S[m] ≡ S[add n m] = fix fun add_succ n m →
//  case n of
//  | Z[u] → {}
//  | S[p] → let ind_hyp = add_succ p m in {}

//val add_succ : ∀n:ι, ∀m:ι, n∈nat ⇒ m∈nat ⇒ add n S[m] ≡ S[add n m] = fix fun add_succ n m →
//  case n of
//  | Z[u] → {}
//  | S[p] → let ind_hyp : add p S[m] ≡ S[add p m] = add_succ p m in {}
