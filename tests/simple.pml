val id_unit  : {} ⇒ {} = λx.x
val fst_unit : {} ⇒ {} ⇒ {} = λx.λy.x
val snd_unit : {} ⇒ {} ⇒ {} = λx.λy.y

val id_lamb : ∀ (t : ο) t ⇒ t = Λ (t : ο) λx.x
val id : ∀ (t : ο) t ⇒ t = λx.x

val fst : ∀ (a : ο) ∀ (b : ο) a ⇒ b ⇒ a = λx.λy.x

val weird_app : (∀ (a : ο) a ⇒ a) ⇒ {} ⇒ {} = λid.λx.id x
