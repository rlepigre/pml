type rec nat = [Z ; S of nat]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

val pred : [S of nat] ⇒ nat = fun n →
  case n { S[n] → n }

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

val rec compare : nat ⇒ nat ⇒ [Ls ; Eq ; Gr] = fun n m →
  case n {
    | Z[_] → case m {
               | Z[_] → Eq
               | S[_] → Ls
             }
    | S[n] → case m {
               | Z[_] → Gr
               | S[m] → compare n m
             }
  }

val eq : nat ⇒ nat ⇒ bool = fun n m →
  case compare n m {
    | Ls[_] → false
    | Eq[_] → true
    | Gr[_] → false
  }

// Examples
val one : nat = succ zero
val two : nat = succ (succ zero)
val six : nat = mul two (succ two)
