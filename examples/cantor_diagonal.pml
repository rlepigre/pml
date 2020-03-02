include lib.nat

// Cantor's diagonal argument
type bot = ∀x,x

val rec lem : ∀n, n∈ nat | n ≡ S[n] → bot =
  fun n {  ✂  }

// Cantor diagonal argument for pure arrow
val diag : ∀idx ∈(nat ⇒ (nat ⇒ nat)),
             (∀f∈(nat ⇒ nat), ∃m, m∈nat | idx m ≡ f) ⇒ bot =
  fun idx xdi {
    let f : nat ⇒ nat = fun n { S[idx n n] };
    let m = xdi f;
    deduce idx m ≡ f;
    let x = f m;
    ✂
  }

val lem : ∀f∈(nat → nat), ∃g∈(nat ⇒ nat), ∀n∈nat, f n ≡ g n =
  fun f {
    let g : nat ⇒ nat = fun n { delim {f n} };
    (g, fun n { let p = delim {f n}; qed })
  }


// Cantor diagonal argument for classical arrow
val cdiag : ∀idx ∈(nat → (nat → nat)),
              (∀f, f∈(nat → nat) → ∃m, m∈nat | idx m ≡ f) → bot =
  fun idx xdi {
    let f : nat → nat = fun n { S[idx n n] };
    let m = xdi f;
    deduce idx m ≡ f;
    let x = delim {f m};
    ✂
  }

val cdiag2: ∀idx ∈(nat ⇒ (nat → nat)),
              (∀f∈(nat → nat), ∃m, m∈nat | idx m ≡ f) ⇒ bot =
  fun idx xdi {
    let f : nat → nat = fun n { S[idx n n] };
    let m = xdi f;
    deduce idx m ≡ f;
    let x = delim {f m};
    ✂
  }
