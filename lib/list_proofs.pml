// Proofs on lists

include lib.list

val rec app_asso : ∀a, ∀x y z∈list<a>, app x (app y z) ≡ app (app x y) z =
  fun l1 l2 l3 {
    case l1 {
            | Nil     →
              let total = app l2 l3;
              {}
            | Cons[c] →
              let hd = c.hd;
              let tl = c.tl;
              let total = app tl l2;
              let total = app l2 l3;
              let ded : app l1 (app l2 l3) ≡ cons hd (app tl (app l2 l3)) = {};
              let ded : app (app l1 l2) l3 ≡ cons hd (app (app tl l2) l3) = {};
              let ind : app tl (app l2 l3) ≡ app (app tl l2) l3 = app_asso tl l2 l3;
              {}
    }
  }

val rec app_nil : ∀a, ∀l∈list<a>, app l [] ≡ l =
  fun l {
    case l {
      []    → {}
      h::l' → use app_nil l'
    }
  }

val rec app_rev_rev1 : ∀a, ∀x y z∈list<a>,
                        rev_app x (rev_app y z) ≡ rev_app (app y x) z =
  fun x y z {
    case y {
      []     → {}
      h::y' →
        deduce rev_app x (rev_app y z) = rev_app x (rev_app y' (h::z));
        use app y' x;
        deduce rev_app (app y x) z ≡ rev_app (app y' x) (h::z);
        use app_rev_rev1 x y' (h::z)
    }
  }

val rec app_rev_rev2 : ∀a, ∀x y z∈list<a>,
                        rev_app (rev_app x y) z ≡ rev_app y (app x z) =
  fun x y z {
    case x {
      []     → {}
      h::x' →
        deduce rev_app (rev_app x y) z ≡ rev_app (rev_app x' (h::y)) z;
        show rev_app (rev_app x' (h::y)) z ≡ rev_app (h::y) (app x' z)
          using app_rev_rev2 x' (h::y) z;
        use app x' z;
        deduce rev_app y (app x z) ≡ rev_app y (h::(app x' z))
    }
  }

val rev_rev : ∀a, ∀x∈list<a>, rev (rev x) ≡ x =
  fun x {
    use rev_app x [];
    deduce rev (rev x) ≡ rev_app (rev_app x []) [];
    show rev (rev x) ≡ rev_app [] (app x []) using app_rev_rev2 x [] [];
    use app_nil x
  }

def cmp<f:ι,g:ι> = fun x { g (f x) }

val map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), ∀l∈list<a>,
                map g (map f l) ≡ map cmp<f,g> l =
    fun fn gn {
      fix fun map_map ls {
        case ls {
                | Nil     → {}
                | Cons[c] →
                  let fc = fn c.hd;
                  use gn fc;
                  use map fn c.tl;
                  let ind = map_map c.tl; {}
        }
      }
    }

val rec map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), ∀l∈list<a>,
                    map g (map f l) ≡ map cmp<f,g> l =
    fun fn gn ls {
      case ls {
              | Nil     → {}
              | Cons[c] →
                let fc = fn c.hd;
                use gn fc;
                use map fn c.tl;
                let ind : map gn (map fn c.tl) ≡ map cmp<fn,gn> c.tl =
                  map_map fn gn c.tl;
                {}
      }
    }
