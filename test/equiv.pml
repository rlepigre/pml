val refl1 : {} ≡ {} = {}
val refl2 : (λx.x) ≡ (λx.x) = {}
val refl3 : C[{}] ≡ C[{}] = {}

val refl_v : ∀ (x : ι) x ≡ x = {}
val refl_t : ∀ (a : τ) a ≡ a = {}

val symm_v : ∀ (x : ι) ∀ (y : ι) x ≡ y ⇒ y ≡ x = λx.x
val symm_t : ∀ (a : τ) ∀ (b : τ) a ≡ b ⇒ b ≡ a = λx.x

//val symm_v2 : ∀ (x : ι) ∀ (y : ι) x ≡ y ⇒ y ≡ x = λx.{}
//val symm_t2 : ∀ (a : τ) ∀ (b : τ) a ≡ b ⇒ b ≡ a = λx.{}
