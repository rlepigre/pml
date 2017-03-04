// Unit type.
type unit = {}

// Booleans.
type bool = [Tru ; Fls]

val tru : bool = Tru[]
val fls : bool = Fls[]

// More usual names for the booleans.
val true  : bool = Tru[]
val false : bool = Fls[]

def cond<c,t,e> =
  case c of
  | Tru[] → t
  | Fls[] → e

val and : bool ⇒ bool ⇒ bool = fun a b → cond<a, b, fls>

val or  : bool ⇒ bool ⇒ bool = fun a b → cond<a, tru, b>

// Option type.
type option<a> = [None ; Some of a]

val none : ∀a, option<a> = None[{}]
val some : ∀a, a ⇒ option<a> = fun e → Some[e]

val map_opt : ∀a b, (a ⇒ b) ⇒ option<a> ⇒ option<b> = fun fn o →
  case o of
  | None[_] → none
  | Some[e] → some (fn e)
