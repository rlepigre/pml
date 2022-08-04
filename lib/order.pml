include lib.bool
include lib.list

type rel⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool); ⋯}

type preorder⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; refl  : ∀x∈a, cmp x x
  ; trans : ∀x y z∈a, cmp x y ⇒ cmp y z ⇒ cmp x z; ⋯ }

type order⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; refl  : ∀x∈a, cmp x x
  ; trans : ∀x y z∈a, cmp x y ⇒ cmp y z ⇒ cmp x z
  ; anti  : ∀x y∈a, cmp x y ⇒ cmp y x ⇒ x ≡ y; ⋯ }

type total_preorder⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; refl  : ∀x∈a, cmp x x
  ; trans : ∀x y z∈a, cmp x y ⇒ cmp y z ⇒ cmp x z
  ; total : ∀x y∈a, cmp x y || cmp y x; ⋯ }

type total_order⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; refl  : ∀x∈a, cmp x x
  ; trans : ∀x y z∈a, cmp x y ⇒ cmp y z ⇒ cmp x z
  ; anti  : ∀x y∈a, cmp x y ⇒ cmp y x ⇒ x ≡ y
  ; total : ∀x y∈a, cmp x y || cmp y x; ⋯ }

// Order relation on natural numbers.

include lib.nat
include lib.nat_proofs

val nat_order : total_order⟨nat⟩ =
  { cmp = leq, refl = leq_refl, trans = leq_trans,
    total = leq_total, anti = leq_anti }

val nat_rev_order : total_order⟨nat⟩ =
  { cmp = geq, refl = geq_refl, trans = geq_trans,
    total = geq_total, anti = geq_anti }
