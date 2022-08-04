// "Append list" (lists with constant time concatenation)

include lib.list

type rec alist⟨a⟩ =
  [Nil
  ; Cons of {hd : a ; tl : alist⟨a⟩}
  ; Append of {l : alist⟨a⟩; r : alist⟨a⟩}]

val alist_app : ∀a, alist⟨a⟩ ⇒ alist⟨a⟩ ⇒ alist⟨a⟩ =
  fun l r { Append[{l,r}] }

val list_to_alist : ∀a, list⟨a⟩ ⇒ alist⟨a⟩ =
  fun l { l }

val rec alist_to_list : ∀a, alist⟨a⟩ ⇒ list⟨a⟩ =
  fun l {
    case l {
      []        → []
      h::l      → h::alist_to_list l
      Append[c] → alist_to_list c.l @ alist_to_list c.r
    }
  }
