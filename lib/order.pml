include lib.bool
include lib.list

type ord<a> = ∃cmp,
  { cmp   : cmp ∈ (a ⇒ a ⇒ bool)
  ; trans : ∀x y z∈a, (cmp x y ≡ true ⇒ cmp y z ≡ true ⇒ cmp x y ≡ true)
  ; total : ∀x y∈a, or (cmp x y) (cmp y x) ≡ true }

val rec sorted : ∀a, ∀o∈ord<a>, ∀l∈list<a>, bool =
  fun o l {
    case l {
      Nil      → true
      Cons[c1] →
        let hd = c1.hd;
        let tl = c1.tl;
        case tl {
          Nil      → true
          Cons[c2] →
            let hd2 = c2.hd;
            land<o.cmp hd hd2, sorted o tl>
        }
    }
  }

type slist<a,o> = {l∈list<a> | sorted o l ≡ true}

val tl : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      Nil → Nil
      Cons[c] → c.tl
    }
  }

val tl_sorted : ∀a, ∀o∈ord<a>, ∀l∈slist<a,o>, sorted o (tl l) ≡ true =
  fun o l {
    case l {
      Nil →
        let _ : tl l ≡ Nil = {};
        {}
      Cons[c1] →
        let tl1 = c1.tl;
        deduce tl l ≡ tl1;
        let hd1 = c1.hd;
        case tl1 {
          Nil → {}
          Cons[c2] →
            let hd2 = c2.hd;
            if o.cmp hd1 hd2 { {} } else { ✂ }
        }
    }
  }
