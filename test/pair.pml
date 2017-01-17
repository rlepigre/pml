def prod (a : ο) (b : ο) = ∀ (x : ο) (a ⇒ b ⇒ x) ⇒ x

val pair : ∀ (a : ο) ∀ (b : ο) a ⇒ b ⇒ prod<a,b> = λx.λy.λp.p x y

// val pair = λx.λy.λp.p x y
