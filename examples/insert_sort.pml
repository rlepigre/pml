include lib.order
include lib.list
include lib.list_sorted
// remark: we do not use transitivity in the example

val rec insert : ∀a:ο, rel⟨a⟩ ⇒ a ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun o x l {
    case l {
      Nil     → Cons[{hd = x; tl = Nil}]
      Cons[c] → let hd = c.hd; let tl = c.tl;
                if o.cmp x hd {
                  Cons[{hd = x ; tl = l}]
                } else {
                  let tl = insert o x tl;
                  Cons[{hd = hd ; tl = tl}]
                }
    }
  }

val rec isort : ∀a:ο, rel⟨a⟩ ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun o l {
    case l {
      Nil     → Nil
      Cons[c] → insert o c.hd (isort o c.tl)
    }
  }

val rec insert_sorted : ∀a:ο, ∀o∈total_preorder⟨a⟩, ∀x∈a, ∀l∈slist⟨a,o⟩,
                  sorted o (insert o x l) ≡ true =
  fun o x l {
    case l {
      Nil      → {}
      Cons[c1] →
        if o.cmp x c1.hd { {} }
        else {
          use o.cmp c1.hd x;
          use o.total x c1.hd;
          case c1.tl {
            Nil      → {}
            Cons[c2] →
              use insert o x c2.tl;
              if o.cmp c1.hd c2.hd {
                deduce sorted o c1.tl ≡ true;
                use insert_sorted o x c1.tl;
                  if o.cmp x c2.hd { {} } else { {} }
              } else { ✂ }
          }
        }
    }
  }

val rec isort_sorted : ∀a:ο, ∀o∈total_preorder⟨a⟩, ∀l∈list⟨a⟩,
                       sorted o (isort o l) ≡ true =
  fun o l {
    case l {
      Nil     → {}
      Cons[c] →
        use isort_sorted o c.tl;
        use insert_sorted o c.hd (isort o c.tl)
    }
  }

val isort_full : ∀a:ο, ∀o∈total_preorder⟨a⟩, list⟨a⟩ ⇒ slist⟨a,o⟩ =
  fun o l {
    let tot = isort o l;
    let lem = isort_sorted o l;
    isort o l
  }
