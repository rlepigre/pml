include lib.either

val pierce : ∀ a b, ((a ⇒ b) ⇒ a) ⇒ a =
  fun x → save a → x (fun y → restore a y)

type bot = ∀x, x
type neg<a> = a ⇒ bot

val excl_mid : ∀ a, {} ⇒ either<a, neg<a>> =
  fun _ → save k → InR[fun x → restore k InL[x]]

val dneg_elim : ∀ a, neg<neg<a>> ⇒ a = pierce
