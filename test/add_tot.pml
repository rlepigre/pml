type rec nat = [Zero ; Succ of nat]

def t_add : ι =
  fix fun add n m →
    case n of
    | Zero[_] → m
    | Succ[k] → Succ[add k m]

val add_basic : nat ⇒ nat ⇒ nat = t_add

val add : ∀n m∈nat, ∃k:ι, k∈(nat | t_add n m ≡ k) = t_add

// Attempt to use a stronger type for add.
//val rec add_asso : ∀n m p∈nat, add n (add m p) ≡ add (add n m) p =
//  fun n m p →
//    case n of
//    | Zero[_] → {}
//    | Succ[k] → let ih = add_asso k m p in {}

// Proof by induction.
//val rec ind : ∀f:ι→ο, f<Zero> ⇒ (∀i∈nat, f<i> ⇒ f<Succ[i]>) ⇒ ∀n∈nat, f<n> =
//  fun d s n →
//    case n of
//    | Zero[_] → d
//    | Succ[k] → s k (ind d s k)
