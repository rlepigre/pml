type rec nat = [Z ; S of nat]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Z[_] → m
    | S[k] → succ (add k m)
  }

val rec mul : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Z[_] → zero
    | S[k] → add m (mul k m)
  }

val rec pred : [S of nat] ⇒ nat = fun n →
  case n { S[n] → n }

val rec eq : nat ⇒ nat ⇒ bool = fun n m →
  case n {
    | Z[_] → case m {
               | Z[_] → true
               | S[_] → false
             }
    | S[n] → case m {
               | Z[_] → false
               | S[m] → eq n m
             }
  }

// Examples
val one : nat = succ zero
val two : nat = succ (succ zero)
val six : nat = mul two (succ two)
