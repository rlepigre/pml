
type rec nat = [ Zero ; S of nat ]

val zero : nat = Zero
val succ : nat ⇒ nat = fun n { S[n] }
val rec dble : nat ⇒ nat = fun n { case n { 0 → 0 | S[p] → S[S[p]] } }

type rec int = [ Zero ; S of nat ; N of nat ]

type rec rat = [ Zero ; S of nat ; N of nat ; F of int × nat ]

val rec ge_nat : nat ⇒ nat ⇒ bool = fun n m {
  case n {
    0     → false
    S[n'] → case m {
      0     → true
      S[m'] → ge_nat n' m'
    }
  }
}
val le_nat : nat ⇒ nat ⇒ bool = fun n m { ge_nat m n }

val rec ge : int ⇒ int ⇒ bool = fun n m {
  case n {
    0     →
      case m {
        0      → false
        S[m']  → false
        N[m'] → true
      }
    S[n'] →
      case m {
        0     → true
        S[m'] → ge_nat n' m'
        N[m'] → true
      }
    N[n'] →
      case m {
        0     → false
        S[m'] → false
        N[m'] → le_nat n' m'
      }
  }
}

infix (>) = ge priority 5 non associative

val gcd : int ⇒ int ⇒ int = {-Lets do gcd later-}

type fraction = { numer : int ; denom : { n∈nat | n > 1 } }

type rec qnr = [ Zero ; S of int ; N of nat ; F of fraction ]

type reduced = { q ∈ fraction | gcd q.numer q.denom ≡ 1 }

type rec q = [ Zero ; S of int ; N of nat ; F of reduced ]

check nat ⊂ int
check int ⊂ q
check q ⊂ qnr

val test1 : { b∈bool | b ≡ true } = 2 > 1

check  { n∈nat | n > 1 } ⊂ [ S of [ S of nat ] ]

val plus2 : nat →  { n∈nat | n > 1 } = fun n { S[S[n]] }

//Two things that do not work yet.

//val plus1 : { n∈nat | n > 0 } →  { n∈nat | n > 1 } = fun n { S[n] }

//check [ S of [ S of nat ] ] ⊂ { n∈nat | n > 1 }
