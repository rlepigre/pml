def prod (a : ο) (b : ο) = ∀ (x : ο) (a ⇒ b ⇒ x) ⇒ x

val pair : ∀ (a : ο) ∀ (b : ο) a ⇒ b ⇒ prod<a,b> = λx.λy.λp.p x y

val fst : ∀ (a : ο) ∀ (b : ο) prod<a,b> ⇒ a = λp.p (λx.λy.x)
val snd : ∀ (a : ο) ∀ (b : ο) prod<a,b> ⇒ b = λp.p (λx.λy.y)

// Inference does not work yet because of the strong application rule.
//val pair = λx.λy.λp.p x y
