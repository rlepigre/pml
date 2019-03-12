include lib.nat

val rec is_odd : nat ⇒ bool =
  fun n {
    case n {
      Zero → false
      S[p] →
        case p {
          Zero → true
          S[p] → is_odd p
        }
    }
  }

type odds  = ∃v:ι, v∈nat | is_odd v ≡ true
type evens = ∃v:ι, v∈nat | is_odd v ≡ false

val  odds_to_nat : odds  ⇒ nat = fun x { x }
val evens_to_nat : evens ⇒ nat = fun x { x }

val rec mul2 : nat ⇒ evens =
  fun n {
    case n {
      Zero → Zero
      S[p] → let r : evens = mul2 p; S[S[r]]
    }
  }

val rec succ_even : ∀n∈evens, is_odd S[n] ≡ true =
  fun n {
    case n {
      Zero → {}
      S[p] →
        case p {
          Zero → ✂
          S[r] → succ_even r
        }
    }
  }

val rec succ_even_unrelevant : ∀n∈evens, succ_even n ≡ {} =
  fun n {
    case n {
      Zero → {}
      S[p] →
        case p {
          Zero → ✂
          S[r] → succ_even_unrelevant r
        }
    }
  }

val blop : ∀n∈evens, {} = succ_even_unrelevant

val rec succ_odd  : ∀n∈odds , is_odd S[n] ≡ false =
  fun n {
    case n {
      Zero → ✂
      S[p] →
        case p {
          Zero → {}
          S[r] → succ_odd r
        }
    }
  }

val succ_even : evens ⇒ odds =
  fun x { let h = succ_even x; S[x] }

val succ_odd  : odds  ⇒ evens =
  fun x { let h = succ_odd  x; S[x] }

val succ : nat ⇒ nat = fun x { x }
