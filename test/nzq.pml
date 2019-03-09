include lib.nat

val rec dble : nat ⇒ nat = fun n { case n { 0 → 0 | S[p] → S[S[p]] } }

type rec int = [ Zero ; S of nat ; N of nat ]

type rec rat = [ Zero ; S of nat ; N of nat ; F of int × nat ]

type fraction = { numer : int ; denom : { n∈nat | n > 1 } }

type rec qnr = [ Zero ; S of int ; N of nat ; F of fraction ]

type reduced = { q ∈ fraction | gcd q.numer q.denom ≡ 1 }

type rec q = [ Zero ; S of int ; N of nat ; F of reduced ]

assert nat ⊂ int
assert int ⊂ q
assert q ⊂ qnr

val test1 : { b∈bool | b ≡ true } = 2 > 1

assert  { n∈nat | n > 1 } ⊂ [ S of [ S of nat ] ]

val plus2 : nat →  { n∈nat | n > 1 } = fun n { S[S[n]] }

//Two things that do not work yet.

//val plus1 : { n∈nat | n > 0 } →  { n∈nat | n > 1 } = fun n { S[n] }

//assert [ S of [ S of nat ] ] ⊂ { n∈nat | n > 1 }
