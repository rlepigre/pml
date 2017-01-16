val id = λx.x

val fst = λx.λy.x
val snd = λx.λy.y
// val cpl = λx.λy.λp.p x y

val cpl : ∀ (a : ο) ∀ (b : ο) ∀ (c : ο) a ⇒ b ⇒ (a ⇒ b ⇒ c) ⇒ c = λx.λy.λp.p x y

val cpl = λx.λy.{x = x; y = y}

// val delta = λx.x x

val pierce = λx.μa.x (λy.[a]y)
