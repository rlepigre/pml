include lib.nat

// Cantor's diagonal argument
type bot = ∀x,x

val rec lem : ∀n, n∈ nat | n ≡ S[n] → bot =
  fun n {  ✂  }

val id : ∀x,x ⇒ x = fun x { x }

val id_is_id : ∀a,∀x∈a, id x ≡ x = fun x { {} }

close id // trick to avoid PML looping

val diag : ∀idx ∈(nat ⇒ (nat ⇒ nat)),  (∀f∈(nat ⇒ nat), ∃m, m∈nat | idx (id m) ≡ f) ⇒ bot =
  fun idx xdi {
    let f : nat ⇒ nat = fun n { S[idx n n] };
    let m = xdi f;
    deduce idx (id m) ≡ f;
    let x = f m;
    show x ≡ S[f m] using id_is_id x;
    ✂
  }

// remark proving the diagonal arument for the classical arrow is much more difficult
// we get a fixpoint of successor f x = succ (f x), which is not a contradiction
// in itself as f x is not a value. After all, such a fixpoint exists. The contradiction
// should come from the fact that f x : nat, but induction only prove results about values

open id
