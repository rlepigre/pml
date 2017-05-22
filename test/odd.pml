include lib.nat

val rec is_odd : nat ⇒ bool = fun n →
  case n {
    Z[_] → false
    S[p] →
      case p {
        Z[_] → true
        S[p] → is_odd p
      }
  }

type odds  = ∃v:ι, v∈nat | is_odd v ≡ true
type evens = ∃v:ι, v∈nat | is_odd v ≡ false

val  odds_to_nat : odds  ⇒ nat = fun x → x
val evens_to_nat : evens ⇒ nat = fun x → x

val rec mul2 : nat ⇒ evens = fun n →
  case n {
    Z[_] → Z
    S[p] → let r : evens = mul2 p in
           S[S[r]]
  }

val rec succ_even : ∀n∈evens, is_odd S[n] ≡ true  = fun n →
  case n {
    Z[_] → {}
    S[p] →
      case p {
        Z[_] → ✂
        S[r] → succ_even r
      }
  }

val rec succ_odd  : ∀n∈odds , is_odd S[n] ≡ false = fun n →
  case n {
    Z[_] → ✂
    S[p] →
      case p {
        Z[_] → {}
        S[r] → succ_odd r
      }
  }

val succ_even : evens ⇒ odds  = fun x →
  let h = succ_even x in S[x]

val succ_odd  : odds  ⇒ evens = fun x →
  let h = succ_odd  x in S[x]
