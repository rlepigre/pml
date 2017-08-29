include lib.list

val rec id : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      Nil     → nil
      Cons[c] → Cons[{hd = c.hd; tl = id c.tl}]
    }
  }

val rec id : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      Nil           → nil
      Cons[{hd;tl}] → cons hd (id tl)
    }
  }

val rec id : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      Nil                → nil
      Cons[{hd=x;tl=xs}] → cons x (id xs)
    }
  }

val rec id : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      []    → nil
      x::xs → cons x (id xs)
    }
  }

val rec id : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      []    → [.]
      x::xs → x::(id xs) // FIXME should work without parenthesis
    }
  }
