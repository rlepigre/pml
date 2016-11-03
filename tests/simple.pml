val id_unit  : {} ⇒ {} = λx.x
val fst_unit : {} ⇒ {} ⇒ {} = λx.λy.x
val snd_unit : {} ⇒ {} ⇒ {} = λx.λy.y

val id_lamb : ∀ (t : ο) t ⇒ t = Λ (t : ο) λx.x
val id : ∀ (t : ο) t ⇒ t = λx.x

val fst : ∀ (a : ο) ∀ (b : ο) a ⇒ b ⇒ a = λx.λy.x

val weird_app : (∀ (a : ο) a ⇒ a) ⇒ {} ⇒ {} = λid.λx.id x

val pair : ∀ (a : ο) ∀ (b : ο) a ⇒ b ⇒ {x : a; y : b} = λx.λy.{x = x; y = y}
val pfst : ∀ (a : ο) ∀ (b : ο) {x : a; y : b} ⇒ a = λp.p.x
val psnd : ∀ (a : ο) ∀ (b : ο) {x : a; y : b} ⇒ b = λp.p.y

// Projection of a term
val psnd_trm : ∀ (a : ο) ∀ (b : ο) {x : a; y : b} ⇒ b = λp.((λx.x) p).y

val none : ∀ (a : ο) a ⇒ [None of {} ; Some of a] = λx.Some[x]

//val from_opt : ∀ (a : ο) [None of {} ; Some of a] ⇒ a ⇒ a =
//  λxo.λd.case xo of | None[x] → d | Some[x] → x
    
// Option type
def option (a : ο) : ο = [None of {} ; Some of a]
val none : ∀ (a : ο) a ⇒ option(a) = λx.Some[x]


