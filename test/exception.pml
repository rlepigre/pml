include lib.bool
include lib.list

type bot = ∀x, x
type neg<a> = a → bot

val rec exists : ∀a:ο, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun f l {
    case l {
      Nil[_]  → false
      Cons[c] → if f c.hd { true } else { exists f c.tl }
    }
  }

val total : ∀a b, ∀f∈a⇒b, ∀x∈a, ∃v:ι, v ∈ b | v ≡ f x =
  fun f x { let y = f x; y }

val rec find : ∀a:ο, ∀f∈(a ⇒ bool),
                       ∀l∈list<a>, neg<(exists f l ≡ false)> → a =
  fun f l exc {
    case l {
      | Nil[_]  → exc {}
      | Cons[c] → let hd = c.hd; let tl = c.tl;
                  use total f hd;
                  if f hd { hd } else { find f tl exc }
    }
  }

val find_opt : ∀a:ο, ∀f∈(a ⇒ bool), list<a> → option<a> =
  fun f l {
    save a {
      Some[find f l (fun _ { restore a none })]
    }
  }

val notNone : ∀a:ο, option<a> ⇒ bool =
  fun o { case o { None → false | Some[_] → true } }

val rec find2 : ∀a:ο, ∀f∈(a ⇒ bool), list<list<a>> → option<a> =
  fun f ls {
    case ls {
      Nil     → none
      Cons[c] →
        save a {
          Some[find f c.hd (fun _ { restore a (find2 f c.tl) })]
        }
    }
  }


// val find_opt2 : ∀a:ο, ∀f∈(a ⇒ bool), ∀l:ι, l∈list<a> →
//                 ∃o:ι, option<a> | imp (exists f l) (notNone o) ≡ tru =
//   fun f l {
//      let test = total (exists f) l;
//      if test {
//       {-save a { Some[find f l (fun _ { restore a none })] -} }
//      else { none }  }
