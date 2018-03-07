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
  ; total : ∀x y∈a, lor⟨cmp x y,cmp y x⟩ ≡ true; ⋯ }

type total_order⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; refl  : ∀x∈a, cmp x x
  ; trans : ∀x y z∈a, cmp x y ⇒ cmp y z ⇒ cmp x z
  ; anti  : ∀x y∈a, cmp x y ⇒ cmp y x ⇒ x ≡ y
  ; total : ∀x y∈a, cmp x y || cmp y x; ⋯ }

val rec sorted : ∀a, ∀o∈rel⟨a⟩, ∀l∈list⟨a⟩, bool =
  fun o l {
    case l {
      Nil      → true
      Cons[c1] →
        let hd = c1.hd;
        let tl = c1.tl;
        case tl {
          Nil      → true
          Cons[c2] →
            let hd2 = c2.hd;
            land⟨o.cmp hd hd2, sorted o tl⟩
        }
    }
  }

type slist⟨a,o⟩ = {l∈list⟨a⟩ | sorted o l }

val tl : ∀a, list⟨a⟩ ⇒ list⟨a⟩ =
  fun l {
    case l {
      Nil → Nil
      Cons[c] → c.tl
    }
  }

val tl_sorted : ∀a, ∀o∈rel⟨a⟩, ∀l∈slist⟨a,o⟩, sorted o (tl l) =
  fun o l { set auto 3 3; qed }

include lib.nat
include lib.nat_proofs

val nat_order : total_order⟨nat⟩ =
  { cmp = leq; refl = leq_refl; trans = leq_trans;
    total = leq_total; anti = leq_anti }

val nat_rev_order : total_order⟨nat⟩ =
  { cmp = geq; refl = geq_refl; trans = geq_trans;
    total = geq_total; anti = geq_anti }
