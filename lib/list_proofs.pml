// Proofs on lists

include lib.list

val rec app_asso : ∀a, ∀x y z∈list⟨a⟩, app x (app y z) ≡ app (app x y) z =
  fun l1 l2 l3 {
    case l1 {
            | []       → {}
            | hd :: tl →
              deduce app l1 (app l2 l3) ≡ cons hd (app tl (app l2 l3));
              deduce app (app l1 l2) l3 ≡ cons hd (app (app tl l2) l3);
              show   app tl (app l2 l3) ≡ app (app tl l2) l3
                using app_asso tl l2 l3;
              {}
    }
  }

val rec app_nil : ∀a, ∀l∈list⟨a⟩, app l [] ≡ l =
  fun l {
    case l {
      []    → {}
      h::l' → use app_nil l'
    }
  }

val rec app_rev_rev1 : ∀a, ∀x y z∈list⟨a⟩,
                        rev_app x (rev_app y z) ≡ rev_app (app y x) z =
  fun x y z {
    case y {
      []     → {}
      h::y' →
        deduce rev_app x (rev_app y z) ≡ rev_app x (rev_app y' (h::z));
        deduce rev_app (app y x) z ≡ rev_app (app y' x) (h::z);
        use app_rev_rev1 x y' (h::z)
    }
  }

val rec app_rev_rev2 : ∀a, ∀x y z∈list⟨a⟩,
                        rev_app (rev_app x y) z ≡ rev_app y (app x z) =
  fun x y z {
    case x {
      []     → {}
      h::x' →
        deduce rev_app (rev_app x y) z ≡ rev_app (rev_app x' (h::y)) z;
        show rev_app (rev_app x' (h::y)) z ≡ rev_app (h::y) (app x' z)
          using app_rev_rev2 x' (h::y) z;
        deduce rev_app y (app x z) ≡ rev_app y (h::(app x' z))
    }
  }

val rev_rev : ∀a, ∀x∈list⟨a⟩, rev (rev x) ≡ x =
  fun x {
    deduce rev (rev x) ≡ rev_app (rev_app x []) [];
    show rev (rev x) ≡ rev_app [] (app x []) using app_rev_rev2 x [] [];
    use app_nil x
  }

def cmp⟨f:ι,g:ι⟩ = fun x { g (f x) }

val map_def : ∀a b, ∀f∈(a ⇒ b), ∀x∈a, ∀l∈list⟨a⟩,
                map f (x::l) ≡ f x :: map f l =
  fun f x l { qed }

val map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), ∀l∈list⟨a⟩,
                map g (map f l) ≡ map cmp⟨f,g⟩ l =
    fun fn gn {
      fix map_map {
        fun ls {
          case ls {
                  | []     → {}
                  | hd::tl → use map_map tl; {}
          }
        }
      }
    }

val rec map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), ∀l∈list⟨a⟩,
                    map g (map f l) ≡ map cmp⟨f,g⟩ l =
    fun fn gn ls {
      case ls {
              | []     → {}
              | hd::tl →
                show map gn (map fn tl) ≡ map cmp⟨fn,gn⟩ tl
                  using map_map fn gn tl;
                {}
      }
    }
