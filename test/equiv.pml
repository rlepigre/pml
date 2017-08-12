val refl1 : {} ≡ {} = {}
val refl2 : (fun x → x) ≡ (fun x → x) = {}
val refl3 : C[{}] ≡ C[{}] = {}

val refl_v : ∀ x:ι, x ≡ x = {}
val refl_t : ∀ a:τ, a ≡ a = {}

val symm_v : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ y ≡ x = fun x → {}
val symm_t : ∀ a:τ, ∀ b:τ, a ≡ b ⇒ b ≡ a = fun x → {}

val symm_v2 : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ y ≡ x = fun x → x
val symm_t2 : ∀ a:τ, ∀ b:τ, a ≡ b ⇒ b ≡ a = fun x → x

val tran_v : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = fun x y → {}
val tran_t : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = fun x y → {}

val tran_v2 : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = fun x y → x
val tran_t2 : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = fun x y → x
val tran_v3 : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = fun x y → y
val tran_t3 : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = fun x y → y

val cons_neq : ∀ x:ι, ∀ y:ι, C[x] ≠ D[y] = {}

val cons_eq  : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ C[x] ≡ C[y] = fun x → {}
val cons_eq2 : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ C[x] ≡ C[y] = fun x → x

val id_eq : ∀ y:ι, ((fun x → x) y) ≡ y = {}
