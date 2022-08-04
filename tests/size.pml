
type rec list⟨a⟩ = [ Nil ; Cons of { hd : a; tl : list⟨a⟩}  ]

val cons : ∀a b, a ⇒ b ⇒ [ Cons of { hd : a; tl : b} ] =
  fun hd tl { Cons[{hd,tl}] }

val rec map : ∀a b, ((a ⇒ b) ⇒ list⟨a⟩ ⇒ list⟨b⟩) =
  fun f l {
    case l {
      Nil → Nil
      x::l → f x :: map f l
    }
  }

// val rec map_biz : ∀a, ((a ⇒ a) ⇒ list⟨a⟩ ⇒ list⟨a⟩) =
//   fun f l {
//     case l {
//       Nil → Nil
//       x::l → f x :: map_biz f (map_biz f l)
//     }
//   }

val rec map_biz : ∀a,∀s, ((a ⇒ a) ⇒ list^s⟨a⟩ ⇒ list^s⟨a⟩) =
  fun f l {
    case l {
      Nil → Nil
      x::l → f x :: map_biz f (map_biz f l)
    }
  }

type corec stream⟨a⟩ = {} ⇒ [ Cons of { hd : a; tl : stream⟨a⟩} ]

val rec smap : ∀a b, ((a ⇒ b) ⇒ stream⟨a⟩ ⇒ stream⟨b⟩) =
  fun f s _ {
    case s {} {
      x::s → f x :: smap f s
    }
  }


val rec smap_biz : ∀a,∀s, ((a ⇒ a) ⇒ stream^s⟨a⟩ ⇒ stream^s⟨a⟩) =
  fun f s _ {
    case s {} {
      x::s → f x :: smap_biz f (smap_biz f s)
    }
  }

type decimal = μs, νz, [ Z of z ; S of s ]

type real    = νz, μs, [ Z of z ; S of s ]

val test : decimal ⇒ real = fun x { x }
