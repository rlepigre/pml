// Church encoding of the product (pair) type.
def prod2 (a : ο) (b : ο) = ∀ (x : ο) (a ⇒ b ⇒ x) ⇒ x

val couple : ∀ (a : ο) ∀ (b : ο) a ⇒ b ⇒ prod2<a,b> =
  λx.λy.λp.p x y

val fst : ∀ (a : ο) ∀ (b : ο) prod2<a,b> ⇒ a = λp.p (λx.λy.x)
val snd : ∀ (a : ο) ∀ (b : ο) prod2<a,b> ⇒ b = λp.p (λx.λy.y)


// Church encoding of the product (triple) type.
def prod3 (a : ο) (b : ο) (c : ο) = ∀ (x : ο) (a ⇒ b ⇒ c ⇒ x) ⇒ x

val triple : ∀ (a : ο) ∀ (b : ο) ∀ (c : ο) a ⇒ b ⇒ c ⇒ prod3<a,b,c> =
  λx.λy.λz.λp.p x y z

val fst3 : ∀ (a : ο) ∀ (b : ο) ∀ (c : ο) prod3<a,b,c> ⇒ a = λt.t (λx.λy.λz.x)
val snd3 : ∀ (a : ο) ∀ (b : ο) ∀ (c : ο) prod3<a,b,c> ⇒ b = λt.t (λx.λy.λz.y)
val snd3 : ∀ (a : ο) ∀ (b : ο) ∀ (c : ο) prod3<a,b,c> ⇒ c = λt.t (λx.λy.λz.z)


// NOTE: inference does not work (for the program bellow) because of the
//       strong application rule.
// val pair_inf = λx.λy.λp.p x y
