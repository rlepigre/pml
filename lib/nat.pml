type rec nat = [Z ; S of nat]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n of
  | Z[_] → m
  | S[k] → succ (add k m)

val rec mul : nat ⇒ nat ⇒ nat = fun n m →
  case n of
  | Z[_] → zero
  | S[k] → add m (mul k m)

// Examples
val one : nat = succ zero
val two : nat = succ (succ zero)
val six : nat = mul two (succ two)
