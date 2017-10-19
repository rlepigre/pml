// "Append list" (lists with constant time concatenation)

include lib.list

type rec alist<a> =
  [Nil ; Cons of {hd : a ; tl : alist} ; Append of {l : alist; r : alist}]

val alist_app : ∀a, alist<a> ⇒ alist<a> ⇒ alist<a> =
  fun l r { Append[{l;r}] }

val list_to_alist : ∀a, list<a> ⇒ alist<a> =
  fun l { l }

val rec alist_to_list : ∀a, alist<a> ⇒ list<a> =
  fun l {
    case l {
      Nil       → Nil
      Cons[c]   → cons c.hd (alist_to_list c.tl)
      Append[c] → app (alist_to_list c.l) (alist_to_list c.r)
    }
  }
