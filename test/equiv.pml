val refl1 : {} ≡ {} = {}
val refl2 : (λx.x) ≡ (λx.x) = {}
val refl3 : C[{}] ≡ C[{}] = {}

val refl_v : ∀ x:ι, x ≡ x = {}
val refl_t : ∀ a:τ, a ≡ a = {}

val symm_v : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ y ≡ x = λx.{}
val symm_t : ∀ a:τ, ∀ b:τ, a ≡ b ⇒ b ≡ a = λx.{}

val symm_v2 : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ y ≡ x = λx.x
val symm_t2 : ∀ a:τ, ∀ b:τ, a ≡ b ⇒ b ≡ a = λx.x

val tran_v : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = λx.λy.{}
val tran_t : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = λx.λy.{}

val tran_v2 : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = λx.λy.x
val tran_t2 : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = λx.λy.x
val tran_v3 : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = λx.λy.y
val tran_t3 : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = λx.λy.y

val cons_neq : ∀ x:ι, ∀ y:ι, C[x] ≠ D[y] = {}

val cons_eq  : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ C[x] ≡ C[y] = λx.{}
val cons_eq2 : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ C[x] ≡ C[y] = λx.x

val id_eq : ∀ y↓, ((λx.x) y) ≡ y = {}
