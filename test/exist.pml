val ex : ∀a:τ, ∀x↓, x ≡ a ⇒ C[x] ≡ (λy.C[y]) a =
  fun e → e

//val ex : ∀ a:τ, ∃ x↓, x ≡ a ⇒ C[x] ≡ (λy.C[y]) a =
//  fun e → e must fail
