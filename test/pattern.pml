include lib.list

val rec id : ∀a, list<a> ⇒ list<a> =
  fun l {
    case l {
      Nil     → nil
      Cons[c] → cons c.hd (id c.tl)
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
