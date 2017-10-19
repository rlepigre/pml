include lib.option
include lib.nat

type rec list<a> = [Nil ; Cons of {hd : a ; tl : list}]

val nil : ∀a, list<a> = Nil
val cons : ∀a, a ⇒ list<a> ⇒ list<a> =
  fun hd tl { Cons[{hd ; tl}] }

val head : ∀a, list<a> ⇒ option<a> =
  fun l {
    case l {
      Nil        → none
      Cons[{hd}] → some hd
    }
  }

val tail : ∀a, list<a> ⇒ option<list<a>> =
  fun l {
    case l {
      Nil        → none
      Cons[{tl}] → some tl
    }
  }

val rec length : ∀a, list<a> ⇒ nat =
  fun l {
    case l {
      Nil        → zero
      Cons[{tl}] → succ (length tl)
    }
  }

val rec map : ∀a b, (a ⇒ b) ⇒ list<a> ⇒ list<b> =
  fun fn l {
    case l {
      Nil           → nil
      Cons[{hd;tl}] → cons (fn hd) (map fn tl)
    }
  }

val rec fold_left : ∀a b, (a ⇒ b ⇒ a) ⇒ a ⇒ list<b> ⇒ a =
  fun fn acc l {
    case l {
      Nil           → acc
      Cons[{hd;tl}] → fold_left fn (fn acc hd) tl
    }
  }

val sum : list<nat> ⇒ nat = fold_left add zero

val rec app : ∀b, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      Nil           → nil
      Cons[{hd;tl}] → cons hd (app tl l2)
    }
  }
