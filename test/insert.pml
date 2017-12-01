include lib.bool
include lib.list

type order<a:ο> = ∃cmp:ι,
  { cmp : cmp ∈ (a ⇒ a ⇒ bool)
//  ; tra : ∀x y z∈a, (cmp x y ≡ tru ⇒ cmp y z ≡ tru ⇒ cmp x y ≡ tru)
  ; tot : ∀x y∈a, or (cmp x y) (cmp y x) ≡ tru }

val rec sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, bool =
  fun o l {
    case l {
      Nil      → tru
      Cons[c1] →
        let hd = c1.hd; let tl = c1.tl;
        case tl {
          Nil[_]   → tru
          Cons[c2] →
            let hd2 = c2.hd;
            if o.cmp hd hd2 { sorted o tl } else { false }
       }
    }
  }

val rec tail_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈list<a>,
    sorted o Cons[{hd = x ; tl = l}] ≡ tru ⇒
    sorted o l ≡ tru =
  fun o x l _ {
    case l {
      Nil[_]  → {}
      Cons[c] →
        if o.cmp x c.hd { {} } else { ✂ }
    }
  }

val rec insert : ∀a:ο, order<a> ⇒ a ⇒ list<a> ⇒ list<a> =
  fun o x l {
    case l {
      Nil[_]   → Cons[{hd = x; tl = Nil}]
      Cons[c1] →
        let hd = c1.hd; let tl = c1.tl;
        if o.cmp x hd { Cons[{hd = x ; tl = l}] }
        else { let tl = insert o x tl; Cons[{hd = hd ; tl = tl}] }
    }
  }

val rec isort : ∀a:ο, order<a> ⇒ list<a> ⇒ list<a> =
  fun o l {
    case l {
      Nil[_]  → Nil
      Cons[c] → insert o c.hd (isort o c.tl)
    }
  }

type slist<a:ο,ord:τ> = ∃l:ι, l∈(list<a> | sorted ord l ≡ tru)

val rec insert_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈slist<a,o>,
                       sorted o (insert o x l) ≡ tru =
  fun o x l {
    let cmp = o.cmp;
    case l {
      | Nil[_]   → {}
      | Cons[c1] →
         let hd = c1.hd; let tl = c1.tl;
         if cmp x hd {
           let lem = tail_sorted o hd tl {}; {}
         } else {
           let lem : cmp hd x ≡ tru = o.tot x hd;
           case tl {
             | Nil[_]   → {}
             | Cons[c2] →
                let hd2 = c2.hd; let tl2 = c2.tl;
                let _ = insert o x tl2; // FIXME #28: necessary to instanciate l in slist
                if cmp hd hd2 {
                   let lem = insert_sorted o x tl;
                   if cmp x hd2 { {} } else {
                     let lem : (cmp hd2 x) ≡ tru = o.tot x hd2;
                     {}
                   }
                } else { ✂ }
           }
         }
    }
  }

val rec isort_sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>,
    sorted o (isort o l) ≡ tru =
  fun o l {
    case l {
      Nil     → {}
      Cons[c] → let ind = isort_sorted o c.tl;
                let tls = isort o c.tl;
                let lem = insert_sorted o c.hd tls; {}
    }
  }

val isort_full : ∀a:ο, ∀o∈order<a>, list<a> ⇒ slist<a,o> =
  fun o l {
    let _ = isort o l; // FIXME #28: necessary to instanciate l in slist
    let lem = isort_sorted o l;
    isort o l
  }
