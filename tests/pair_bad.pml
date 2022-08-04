// bad (too complex) definition kept as a stress test,
// because it used to fail.
def pair⟨a:ο,b:ο⟩ = ∃v:ι, v ∈ ({ fst : a; snd : b } |
   v ≡ (let fst = v.fst;
        let snd = v.snd; { fst = fst, snd = snd }))

val swap : ∀a b:ο, pair⟨a,b⟩ ⇒ pair⟨b,a⟩ =
  fun x {
    let fst = x.fst;
    let snd = x.snd;
    { fst = snd, snd = fst }
  }

val swap_idempotent :∀a b:ο, ∀x∈pair⟨a,b⟩, swap (swap x) ≡ x = fun x { {} }
