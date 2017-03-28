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

def cond<c:τ,t:τ,e:τ> =
  case (c : bool) {
    | Tru[_] → t
    | Fls[_] → e
  }

def land<a:τ,b:τ> = cond<a,b,fls>
def lor <a:τ,b:τ> = cond<a,tru,b>

val not : bool ⇒ bool = fun a → cond<a, fls, tru>

val and : bool ⇒ bool ⇒ bool = fun a b → cond<a, b, fls>

val or  : bool ⇒ bool ⇒ bool = fun a b → cond<a, tru, b>

val xor : bool ⇒ bool ⇒ bool = fun a b → cond<a, not b, b>

val imp : bool ⇒ bool ⇒ bool = fun a b → cond<a, b, tru>

// Option type.
type option<a> = [None ; Some of a]

val none : ∀a, option<a> = None[{}]
val some : ∀a, a ⇒ option<a> = fun e → Some[e]

val map_option : ∀a b, (a ⇒ b) ⇒ option<a> ⇒ option<b> = fun fn o →
  case o {
    | None[_] → none
    | Some[e] → some (fn e)
  }

// Either type.
type either<a,b> = [InL of a ; InR of b]

val inl : ∀a b, a ⇒ either<a,b> = fun x → InL[x]
val inr : ∀a b, b ⇒ either<a,b> = fun x → InR[x]

val gather : ∀a b c, (a ⇒ c) ⇒ (b ⇒ c) ⇒ either<a,b> ⇒ c = fun f g e →
  case e {
    | InL[x] → f x
    | InR[x] → g x
  }

val map_either : ∀a b c d, (a ⇒ c) ⇒ (b ⇒ d) ⇒ either<a,b> ⇒ either<c,d> =
  fun f g e →
    case e {
      | InL[x] → InL[f x]
      | InR[x] → InR[g x]
    }

// Minimal tactics
def tac_deduce<f:ο> : τ = ({} : f)
def tac_show<f:ο, p:τ> : τ = (p : f)
def tac_use<p:τ> : τ = p
def tac_qed : τ = {}
