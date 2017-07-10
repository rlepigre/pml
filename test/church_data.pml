// Church encoding of the product (pair) type.
def prod2<a:ο, b:ο> : ο = ∀ x : ο, (a ⇒ b ⇒ x) ⇒ x

val couple : ∀ a b : ο, a ⇒ b ⇒ prod2<a,b> =
  λx.λy.λp.p x y

val fst : ∀ a b : ο, prod2<a,b> ⇒ a = λp.p (λx.λy.x)
val snd : ∀ a b : ο, prod2<a,b> ⇒ b = λp.p (λx.λy.y)


// Church encoding of the product (triple) type.
def prod3<a:ο, b:ο, c:ο> : ο = ∀ x : ο, (a ⇒ b ⇒ c ⇒ x) ⇒ x

val triple : ∀ a b c : ο, a ⇒ b ⇒ c ⇒ prod3<a,b,c> =
  λx.λy.λz.λp.p x y z

val prj3_1 : ∀ a b c : ο, prod3<a,b,c> ⇒ a = λt.t (λx.λy.λz.x)
val prj3_2 : ∀ a b c : ο, prod3<a,b,c> ⇒ b = λt.t (λx.λy.λz.y)
val prj3_3 : ∀ a b c : ο, prod3<a,b,c> ⇒ c = λt.t (λx.λy.λz.z)


// Church encoding of sum type (with two elements).
def sum2<a:ο, b:ο> : ο = ∀ x : ο, (a⇒x) ⇒ (b⇒x) ⇒ x

val inl : ∀ a b : ο, a ⇒ sum2<a,b> = λx.λa.λb.a x
val inr : ∀ a b : ο, b ⇒ sum2<a,b> = λx.λa.λb.b x

val match : ∀ a b r : ο, sum2<a,b> ⇒ (a⇒r) ⇒ (b⇒r) ⇒ r = λx.x


// Church encoding of sum type (with three elements).
def sum3<a:ο, b:ο, c:ο> : ο = ∀ x : ο, (a⇒x) ⇒ (b⇒x) ⇒ (c⇒x) ⇒ x

val inj1 : ∀ a b c : ο, a ⇒ sum3<a,b,c> = λx.λa.λb.λc.a x
val inj2 : ∀ a b c : ο, b ⇒ sum3<a,b,c> = λx.λa.λb.λc.b x
val inj3 : ∀ a b c : ο, c ⇒ sum3<a,b,c> = λx.λa.λb.λc.c x

val match3 : ∀ a b c r : ο, sum3<a,b,c> ⇒ (a⇒r) ⇒ (b⇒r) ⇒ (c⇒r) ⇒ r = λx.x


// Some proofs.
val test1 : ∀ a b c:ι, prj3_1 (triple a b c) ≡ a = {}
val test2 : ∀ a b c:ι, prj3_2 (triple a b c) ≡ b = {}
val test3 : ∀ a b c:ι, prj3_3 (triple a b c) ≡ c = {}

// NOTE: cannot yet prove such properties.
// val test : ∀ a b c : ο, ∀ e : ι, e∈prod3<a,b,c> ⇒
//            triple (prj3_1 e) (prj3_2 e) (prj3_3 e) ≡ e =
//   fun x → {}


// NOTE: inference does not work (for the program bellow) because of the
//       strong application rule.
// val pair_inf = λx.λy.λp.p x y
