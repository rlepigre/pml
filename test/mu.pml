val pierce : ∀ a b, ((a ⇒ b) ⇒ a) ⇒ a = λx.μa.x (λy.[a]y)

def bot : ο = ∀x, x

val excl_mid : ∀ a, {} ⇒ either<a, a ⇒ bot> =
  fun u → μk.InR[fun x → [k] InL[x]]

//val dneg_elim : ∀ a, (a ⇒ bot) ⇒ bot = fun f →
