include lib.list
include test.mu

val rec exists : ∀a:ο, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun f l →
    case l of
    | Nil[_]  → false
    | Cons[c] → if f c.hd then true else exists f c.tl

val rec find : ∀a:ο, ∀f∈(a ⇒ bool), ∀l∈list<a>, neg<(exists f l ≡ false)> ⇒ a =
  fun f l exc →
    case l of
    | Nil[_]  → exc
    | Cons[c] → if f c.hd then c.hd else find f c.tl exc
