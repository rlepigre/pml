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

// count of concatenation is the sum of counts.

val rec count_append : ∀a, ∀r∈rel⟨a⟩, ∀e∈a, ∀l1 l2∈list⟨a⟩,
    count r e (l1 @ l2) ≡ count r e l1 + count r e l2 =
  fun r e l1 l2 {
    case l1 {
      []   → qed
      x::l →
        show count r e (l @ l2) ≡ count r e l + count r e l2
          using count_append r e l l2;
        showing count r e (x::(l @ l2))
              ≡ count r e (x::l) + count r e l2;
        if r.cmp e x && r.cmp x e {
          showing S[count r e (l @ l2)]
                ≡ S[count r e l] + count r e l2;
          qed
        } else {
          showing count r e (l @ l2)
                ≡ count r e l + count r e l2;
          qed
        }
    }
  }
