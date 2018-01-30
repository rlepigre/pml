include lib.bool
include lib.list

type ord⟨a⟩ = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; trans : ∀x y z∈a, cmp x y ⇒ cmp y z ⇒ cmp x z
  ; total : ∀x y∈a, lor⟨cmp x y,cmp y x⟩ ≡ true }

val rec sorted : ∀a, ∀o∈ord⟨a⟩, ∀l∈list⟨a⟩, bool =
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

val tl_sorted : ∀a, ∀o∈ord⟨a⟩, ∀l∈slist⟨a,o⟩, sorted o (tl l) =
  fun o l { set auto 3 3; qed }

include lib.nat
include lib.nat_proofs

val nat_order : ord⟨nat⟩ =
  { cmp = leq; trans = leq_trans; total = leq_total }

val nat_rev_order : ord⟨nat⟩ =
  { cmp = geq; trans = geq_trans; total = geq_total }