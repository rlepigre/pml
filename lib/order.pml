include lib.bool
include lib.list

type ord<a:ο> = ∃cmp:ι,
  { cmp : cmp ∈ (a ⇒ a ⇒ bool)
  ; termi : ∀x y∈a, ∃v:ι, cmp x y ≡ v  // Should disappear soon
  ; trans : ∀x y z∈a, (cmp x y ≡ true ⇒ cmp y z ≡ true ⇒ cmp x y ≡ true)
  ; total : ∀x y∈a, or (cmp x y) (cmp y x) ≡ true }

val rec sorted : ∀a:ο, ∀o∈ord<a>, ∀l∈list<a>, bool = fun o l →
  case l {
    | Nil[_]   → true
    | Cons[c1] → let hd = c1.hd in let tl = c1.tl in
                  case tl {
                    | Nil[_]   → true
                    | Cons[c2] → let hd2 = c2.hd in
                                   land<(o.cmp) hd hd2, sorted o tl>
                   }
  }

type slist<a:ο,o:τ> = ∃l:ι, l∈(list<a> | sorted o l ≡ true)
