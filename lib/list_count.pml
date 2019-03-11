include lib.bool
include lib.order
include lib.list
include lib.nat

// Counting the elements of a list given an (ordering) relation.

val rec count : ∀a, rel⟨a⟩ ⇒ a ⇒ list⟨a⟩ ⇒ nat =
  fun r x l {
    case l {
      []   → zero
      y::l → if r.cmp x y && r.cmp y x { S[count r x l] }
             else { count r x l }
    }
  }
