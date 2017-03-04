// Unit type.
type unit = {}

// Booleans.
type bool = [Tru ; Fls]

// Short names for the booleans.
val tru : bool = Tru[{}]
val fls : bool = Fls[{}]

// More usual names for the booleans.
val true  : bool = Tru[{}]
val false : bool = Fls[{}]

def cond<c,t,e> =
  case (c : bool) of
  | Tru[_] → t
  | Fls[_] → e

val and : bool ⇒ bool ⇒ bool = fun a b → cond<a, b, fls>

val or  : bool ⇒ bool ⇒ bool = fun a b → cond<a, tru, b>

// Option type.
type option<a> = [None ; Some of a]

val none : ∀a, option<a> = None[{}]
val some : ∀a, a ⇒ option<a> = fun e → Some[e]

val map_option : ∀a b, (a ⇒ b) ⇒ option<a> ⇒ option<b> = fun fn o →
  case o of
  | None[_] → none
  | Some[e] → some (fn e)

// Either type.
type either<a,b> = [InL of a ; InR of b]

val inl : ∀a b, a ⇒ either<a,b> = fun x → InL[x]
val inr : ∀a b, b ⇒ either<a,b> = fun x → InR[x]

val gather : ∀a b c, (a ⇒ c) ⇒ (b ⇒ c) ⇒ either<a,b> ⇒ c = fun f g e →
  case e of
  | InL[x] → f x
  | InR[x] → g x

val map_eigher : ∀a b c d, (a ⇒ c) ⇒ (b ⇒ d) ⇒ either<a,b> ⇒ either<c,d> =
  fun f g e →
    case e of
    | InL[x] → InL[f x]
    | InR[x] → InR[g x]
