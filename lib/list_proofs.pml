// Proofs on lists

include lib.list

val rec app_total : ∀a, ∀l1 l2 ∈list<a>, ∃v:ι, app l1 l2 ≡ v =
  fun l1 l2 {
    case l1 {
      Nil     → {}
      Cons[c] → use app_total c.tl l2
    }
  }

val rec rev_app_total : ∀a, ∀l1 l2 ∈list<a>, ∃v:ι, rev_app l1 l2 ≡ v =
  fun l1 l2 {
    case l1 {
      Nil     → {}
      Cons[c] →
        use rev_app_total c.tl (c.hd :: l2)
    }
  }

val rev_total : ∀a, ∀l∈list<a>, ∃v:ι, rev l ≡ v =
  fun l { use rev_app_total l [] }

val rec app_asso : ∀a, ∀x y z∈list<a>, app x (app y z) ≡ app (app x y) z =
  fun l1 l2 l3 {
    case l1 {
            | Nil     →
              let total = app_total l2 l3;
              {}
            | Cons[c] →
              let hd = c.hd;
              let tl = c.tl;
              let total = app_total tl l2;
              let total = app_total l2 l3;
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
        use app_total y' x;
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
        deduce rev_app y (app x z) ≡ rev_app y (h::(app x' z));
        use app_total x' z
    }
  }

val rev_rev : ∀a, ∀x∈list<a>, rev (rev x) ≡ x =
  fun x {
    use rev_app_total x [];
    deduce rev (rev x) ≡ rev_app (rev_app x []) [];
    show rev (rev x) ≡ rev_app [] (app x []) using app_rev_rev2 x [] [];
    use app_nil x
  }

def total<f:ι,a> = ∀x∈a, ∃v:ι, f x ≡ v
def cmp<f:ι,g:ι> = fun x { g (f x) }

val compose_total : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
  total<f,a> ⇒ total<g,b> ⇒ total<cmp<f,g>, a> =
    fun f g tf tg a { use tf a; use tg (f a) }

val rec map_total : ∀a b, ∀f∈(a⇒b), total<f,a>
  ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
    fun fn ft ls {
      case ls {
              | Nil     → {}
              | Cons[c] →
                let hd = c.hd;
                let tl = c.tl;
                let lem : (∃v:ι, fn hd ≡ v) = ft hd;
                let ind : (∃v:ι, map fn tl ≡ v) = map_total fn ft tl; {}
      }
    }

val map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
  ∀l∈list<a>, map g (map f l) ≡ map cmp<f,g> l =
    fun fn gn {
      fix map_map { fun tf tg ls {
        case ls {
                | Nil     → {}
                | Cons[c] →
                  let hd = c.hd; let tl = c.tl;
                  let tgf = compose_total fn gn tf tg hd;
                  let lem = tf hd;
                  let lem = map_total fn tf tl;
                  let ind = map_map tf tg tl; {}
        }
      }}
    }

val rec map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
  ∀l∈list<a>, map g (map f l) ≡ map cmp<f,g> l =
    fun fn gn tf tg ls {
      case ls {
              | Nil     → {}
              | Cons[c] →
                let hd = c.hd;
                let tl = c.tl;
                let tgf = compose_total fn gn tf tg;
                let lem : (∃v:ι, map cmp<fn,gn> tl ≡ v) = map_total cmp<fn,gn> tgf tl;
                let lem = tf hd;
                let lem = tg (fn hd);
                let lem = tgf hd;
                let lem = map_total fn tf tl;
                let lem = map_total gn tg (map fn tl);
                let lem = map_total cmp<fn,gn> tgf tl;
                let ind : map gn (map fn tl) ≡ map cmp<fn,gn> tl = map_map fn gn tf tg tl;
                {}
      }
    }

val rec length_total : ∀a:ο, ∀l∈list<a>, ∃v:ι, v ≡ length l =
  fun l {
    case l {
      Nil[_]  → {}
      Cons[c] → let ind = length_total c.tl; {}
    }
  }
