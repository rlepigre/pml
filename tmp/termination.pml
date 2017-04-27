type snat<o:κ> = μo snat [Z ; S of snat]
type nat = snat<∞>

//val zero : nat = Z[{}]
//val succ : nat ⇒ nat = fun n → S[n]

//val rec id : nat ⇒ nat = fun n →
//  case n {
//    Z[_] → Z
//    S[k] → S[id k]
//  }

val rec id : ∀o:κ, snat<o> ⇒ snat<o> = fun n →
  case n {
    Z[_] → Z
    S[k] → S[id k]
  }

//val rec add : nat ⇒ nat ⇒ nat = fun n m →
//  case n {
//    Z[_] → m
//    S[k] → succ (add k m)
//  }
