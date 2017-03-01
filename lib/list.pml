include lib.prelude
include lib.nat

type rec list<a:ο> = [Nil ; Cons of {hd : a ; tl : list}]

val nil : ∀a:ο, list<a> = Nil[{}]
val cons : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun hd tl → Cons[{hd = hd; tl = tl}]

val hd : ∀a:ο, list<a> ⇒ option<a> = fun l →
  case l of
  | Nil[_]  → none
  | Cons[c] → some c.hd

val tl : ∀a:ο, list<a> ⇒ option<list<a>> = fun l →
  case l of
  | Nil[_]  → none
  | Cons[c] → some c.tl

val rec length : ∀a:ο, list<a> ⇒ nat = fun l →
  case l of
  | Nil[_]  → zero
  | Cons[c] → succ (length c.tl)

val rec map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> = fun fn l →
  case l of
  | Nil[_]  → nil
  | Cons[c] → cons (fn c.hd) (map fn c.tl)

val rec fold_left : ∀a b:ο, (a ⇒ b ⇒ a) ⇒ a ⇒ list<b> ⇒ a = fun fn acc l →
  case l of
  | Nil[_]  → acc
  | Cons[c] → fold_left fn (fn acc c.hd) c.tl

val sum : list<nat> ⇒ nat = fold_left add zero
