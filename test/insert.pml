include lib.bool
include lib.list

type order<a:ο> = ∃cmp:ι,
  { cmp : cmp ∈ (a ⇒ a ⇒ bool)
//  ; tra : ∀x y z∈a, (cmp x y ⇒ cmp y z ⇒ cmp x y)
  ; tot : ∀x y∈a, or (cmp x y) (cmp y x) }

val rec sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, bool =
  fun o l {
    case l {
      []     → tru
      hd::tl →
        case tl {
          []       → tru
          hd2::tl2 → if o.cmp hd hd2 { sorted o tl } else { false }
       }
    }
  }

val rec tail_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈list<a>,
     sorted o (x::l) ⇒ sorted o l =
  fun o x l _ {
    case l {
      []     → qed
      hd::tl → know o.cmp x hd; qed
    }
  }

val rec insert : ∀a:ο, order<a> ⇒ a ⇒ list<a> ⇒ list<a> =
  fun o x l {
    case l {
      []     → x::[]
      hd::tl → if o.cmp x hd { x::l } else { hd :: insert o x tl }
    }
  }

val rec isort : ∀a:ο, order<a> ⇒ list<a> ⇒ list<a> =
  fun o l {
    case l {
      []     → []
      hd::tl → insert o hd (isort o tl)
    }
  }

type slist<a:ο,ord:τ> = ∃l:ι, l∈(list<a> | sorted ord l ≡ tru)

val rec insert_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈slist<a,o>,
                       sorted o (insert o x l) =
  fun o x l {
    let cmp = o.cmp;
    case l {
      | []     → qed
      | hd::tl →
         if cmp x hd {
           use tail_sorted o hd tl; qed
         } else {
           show cmp hd x using o.tot x hd;
           case tl {
             | []       → qed
             | hd2::tl2 →
                let _ = insert o x tl2; // FIXME #28: necessary to instanciate l in slist
                know cmp hd hd2;
                show sorted o (insert o x tl) using insert_sorted o x tl;
                if cmp x hd2 { qed } else {
                  show cmp hd2 x using o.tot x hd2;
                  qed
                }
           }
         }
    }
  }

val rec isort_sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, sorted o (isort o l) =
  fun o l {
    case l {
      []     → qed
      hd::tl → use isort_sorted o tl;
               let tls = isort o tl;
               use insert_sorted o hd tls;
               qed
    }
  }

val isort_full : ∀a:ο, ∀o∈order<a>, list<a> ⇒ slist<a,o> =
  fun o l {
    use isort_sorted o l;
    isort o l
  }
