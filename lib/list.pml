include lib.option
include lib.nat

type rec list<a> = [Nil ; Cons of {hd : a ; tl : list}]

val nil : ∀a, list<a> = Nil
val cons : ∀a, a ⇒ list<a> ⇒ list<a> =
  fun hd tl { Cons[{hd ; tl}] }

val hd : ∀a, list<a> ⇒ option<a> =
  fun l {
    case l {
      Nil     → none
      Cons[c] → some c.hd
    }
  }

val tl : ∀a, list<a> ⇒ option<list<a>> =
  fun l {
    case l {
      Nil     → none
      Cons[c] → some c.tl
    }
  }

val rec length : ∀a, list<a> ⇒ nat =
  fun l {
    case l {
      Nil     → zero
      Cons[c] → succ (length c.tl)
    }
  }

val rec map : ∀a b, (a ⇒ b) ⇒ list<a> ⇒ list<b> =
  fun fn l {
    case l {
      Nil     → nil
      Cons[c] → cons (fn c.hd) (map fn c.tl)
    }
  }

val rec fold_left : ∀a b, (a ⇒ b ⇒ a) ⇒ a ⇒ list<b> ⇒ a =
  fun fn acc l {
    case l {
      Nil     → acc
      Cons[c] → fold_left fn (fn acc c.hd) c.tl
    }
  }

val sum : list<nat> ⇒ nat = fold_left add zero

val rec app : ∀b, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      | Nil     → nil
      | Cons[c] → cons c.hd (app c.tl l2)
    }
  }
