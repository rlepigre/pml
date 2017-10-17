
type rec list<a> = [ Nil ; Cons of { hd : a; tl : list}  ]

val rec map : ∀a b, ((a ⇒ b) ⇒ list<a> ⇒ list<b>) =
  fun f l {
    case l {
      Nil → Nil
      x::l → f x :: map f l
    }
  }

type list<a> = μlist, [ Nil ; Cons of { hd : a; tl : list}  ]

// val rec map_biz : ∀a, ((a ⇒ a) ⇒ list<a> ⇒ list<a>) =
//   fun f l {
//     case l {
//       Nil → Nil
//       x::l → f x :: map_biz f (map_biz f l)
//     }
//   }

type slist<a,s> = μ_s list, [ Nil ; Cons of { hd : a; tl : list}  ]

val rec map_biz : ∀a,∀s, ((a ⇒ a) ⇒ slist<a,s> ⇒ slist<a,s>) =
  fun f l {
    case l {
      Nil → Nil
      x::l → f x :: map_biz f (map_biz f l)
    }
  }

type corec stream<a> = {} ⇒ [ Cons of { hd : a; tl : stream} ]

val rec smap : ∀a b, ((a ⇒ b) ⇒ stream<a> ⇒ stream<b>) =
  fun f s _ {
    case s {} {
      x::s → f x :: smap f s
    }
  }

type sstream<a,s> = μ_s stream, {} ⇒ [ Cons of { hd : a; tl : stream}  ]

val rec smap_biz : ∀a,∀s, ((a ⇒ a) ⇒ sstream<a,s> ⇒ sstream<a,s>) =
  fun f s _ {
    case s {} {
      x::s → f x :: smap_biz f (smap_biz f s)
    }
  }

type decimal = μs, νz, [ Z of z ; S of s ]

type real    = νz, μs, [ Z of z ; S of s ]

val test : decimal ⇒ real = fun x { x }
