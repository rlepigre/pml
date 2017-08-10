// Option type.
type option<a> = [None ; Some of a]

val none : ∀a, option<a> = None[{}]
val some : ∀a, a ⇒ option<a> = fun e → Some[e]

val map_option : ∀a b, (a ⇒ b) ⇒ option<a> ⇒ option<b> = fun fn o →
  case o {
    None[_] → none
    Some[e] → some (fn e)
  }
