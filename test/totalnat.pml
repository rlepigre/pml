type rec nat = [ Z ; S of nat ]

val zero : nat = Z[]
val succ : nat ⇒ nat = fun n → S[n]
val one  : nat = succ zero
val two  : nat = succ one

def add0 = fix fun add n m →
  case n {
    | Z[] → m
    | S[p] → let _ = add p m in
             let x = add p m in
             succ x
  }

val add : ∀n m∈nat, ∃v↓, v∈nat | v ≡ add0 n m = add0

val test : add ≡ add0 = {}

val rec add_asso : ∀n m q∈nat, add n (add m q) ≡ add (add n m) q =
    fun n m q →
      let _ = add m q in
      case n {
         | Z[] → {}
         | S[p] →
           let _ = add p (add m q) in
           let _ = add p m in
           let ind_hyp = add_asso p m q in
           {}
      }
