val ex : ∀a:τ, ∀x:ι, x ≡ a ⇒ C[x] ≡ (fun y → C[y]) a =
  fun e → e

//val ex : ∀ a:τ, ∃ x:ι, x ≡ a ⇒ C[x] ≡ (fun y → C[y]) a =
//  fun e → e must fail
