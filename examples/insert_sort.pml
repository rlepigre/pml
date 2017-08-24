include lib.list
include lib.order
// remark: we do not use transitivity in the example

val rec insert : ∀a:ο, ord<a> ⇒ a ⇒ list<a> ⇒ list<a> =
  fun o x l {
    case l {
      Nil     → Cons[{hd = x; tl = Nil}]
      Cons[c] → let hd = c.hd in let tl = c.tl in
                if o.cmp x hd then {
                  Cons[{hd = x ; tl = l}]
                } else {
                  let tl = insert o x tl in
                  Cons[{hd = hd ; tl = tl}]
                }
    }
  }

val rec isort : ∀a:ο, ord<a> ⇒ list<a> ⇒ list<a> =
  fun o l {
    case l {
      Nil     → Nil
      Cons[c] → insert o c.hd (isort o c.tl)
    }
  }

val rec insert_total : ∀a:ο, ∀o∈ord<a>, ∀x∈a, ∀l∈list<a>,
                       ∃v:ι, insert o x l ≡ v =
  fun o x l {
    case l {
      Nil[_]   → {}
      Cons[c1] → let hd = c1.hd in let tl = c1.tl in
                 let lem = o.termi x hd in
                 if o.cmp x hd then {} else insert_total o x tl
    }
  }

val rec isort_total :  ∀a:ο, ∀o∈ord<a>, ∀l∈list<a>,
                       ∃v:ι, isort o l ≡ v =
  fun o l {
    case l {
      | Nil     → {}
      | Cons[c] → let ih  = isort_total o c.tl in
                   let lem = insert_total o c.hd (isort o c.tl) in {}
    }
  }

val rec insert_sorted : ∀a:ο, ∀o∈ord<a>, ∀x∈a, ∀l∈slist<a,o>,
                  sorted o (insert o x l) ≡ true =
  fun o x l {
    case l {
      Nil      → {}
      Cons[c1] →
        let lem = o.termi x c1.hd in
        if o.cmp x c1.hd then  {}
        else {
          let lem = o.termi c1.hd x in
          let lem = o.total x c1.hd in
          case c1.tl {
            Nil      → {}
            Cons[c2] →
              let lem = insert_total o x c2.tl in
              let lem = o.termi c1.hd c2.hd in
              let lem = o.termi x c2.hd in
              if o.cmp c1.hd c2.hd then {
                let lem = insert_sorted o x c1.tl in
                if o.cmp x c2.hd then {} else {}
              } else ✂
          }
        }
    }
  }

val rec isort_sorted : ∀a:ο, ∀o∈ord<a>, ∀l∈list<a>,
                       sorted o (isort o l) ≡ true =
  fun o l {
    case l {
      Nil     → {}
      Cons[c] →
        use { isort_total o c.tl };
        use { isort_sorted o c.tl };
        use { insert_sorted o c.hd (isort o c.tl) }
    }
  }

val isort_full : ∀a:ο, ∀o∈ord<a>, list<a> ⇒ slist<a,o> =
  fun o l {
    let tot = isort_total o l in
    let lem = isort_sorted o l in
    isort o l
  }
