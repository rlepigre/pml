include lib.order
include lib.list
include lib.list_sorted

val tl : ∀a, list⟨a⟩ ⇒ list⟨a⟩ =
  fun l {
    case l {
      Nil → Nil
      Cons[c] → c.tl
    }
  }

val tl_sorted : ∀a, ∀o∈rel⟨a⟩, ∀l∈slist⟨a,o⟩, sorted o (tl l) =
  fun o l { set auto 2 2; qed}
