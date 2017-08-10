type unit = {}
type boolean = [Fls of unit ; Tru of unit]
// type boolean = [Fls ; Tru]
val cond_fun : ∀ a, boolean ⇒ a ⇒ a ⇒ a = fun c e1 e2 →
  case c { Tru[_] → e1 | Fls[_] → e2 }
def cond<c:τ, e1:τ, e2:τ> : τ =
  case c { Tru[_] → e1 | Fls[_] → e2 }
val cond_fun : ∀ a, boolean ⇒ a ⇒ a ⇒ a = fun c e1 e2 →
  cond<c, e1, e2>
def land<b1:τ,b2:τ> =
  case b1 { Tru[_] → b2 | Fls[_] → Fls }

def lor<b1:τ,b2:τ> =
  case b1 { Tru[_] → Tru | Fls[_] → b2 }
val not : boolean ⇒ boolean = fun a →
  case a { Fls[_] → Tru | Tru[_] → Fls }

val or  : boolean ⇒ boolean ⇒ boolean = fun a b → lor <a, b>
val and : boolean ⇒ boolean ⇒ boolean = fun a b → land<a, b>
val imp : boolean ⇒ boolean ⇒ boolean = fun a b → lor <b, not a>

val xor : boolean ⇒ boolean ⇒ boolean = fun a b →
  case a {
    | Fls[_] → case b { Fls[_] → Fls | Tru[_] → Tru }
    | Tru[_] → case b { Fls[_] → Tru | Tru[_] → Fls }
  }

val eq : boolean ⇒ boolean ⇒ boolean = fun a b → xor a (not b)
val excl_mid : ∀x∈boolean, or x (not x) ≡ Tru = fun b →
  case b { Fls[_] → {} | Tru[_] → {} }
val eq_refl : ∀a∈boolean, eq a a ≡ Tru = fun a →
  case a { Fls[_] → {} | Tru[_] → {} }

val eq_comm : ∀a b∈boolean, eq a b ≡ eq b a = fun a b →
  case a {
    | Fls[_] → case b { Tru[_] → {} | Fls[_] → {} }
    | Tru[_] → case b { Tru[_] → {} | Fls[_] → {} }
  }

val eq_asso : ∀a b c∈boolean, eq (eq a b) c ≡ eq a (eq b c) = fun a b c →
  case a {
    | Fls[_] → case b {
                  | Tru[_] → case c { Tru[_] → {} | Fls[_] → {} }
                  | Fls[_] → case c { Tru[_] → {} | Fls[_] → {} }
                }
    | Tru[_] → case b {
                  | Tru[_] → case c { Tru[_] → {} | Fls[_] → {} }
                  | Fls[_] → case c { Tru[_] → {} | Fls[_] → {} }
                } 
  }
def auto1<a:τ>           : τ = cond<a, {}, {}>
def auto2<a:τ, b:τ>      : τ = cond<a, auto1<b>, auto1<b>>
def auto3<a:τ, b:τ, c:τ> : τ = cond<a, auto2<b,c>, auto2<b,c>>

val eq_refl_auto : ∀a∈boolean, eq a a ≡ Tru = fun a → auto1<a>

val eq_comm_auto : ∀a b∈boolean, eq a b ≡ eq b a = fun a b → auto2<a,b>

val eq_asso_auto : ∀a b c∈boolean, eq (eq a b) c ≡ eq a (eq b c) =
  fun a b c → auto3<a,b,c>
