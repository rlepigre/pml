val id_unit  : {} ⇒ {} = fun x → x
val fst_unit : {} ⇒ {} ⇒ {} = fun x y → x
val snd_unit : {} ⇒ {} ⇒ {} = fun x y → y

val id_lamb : ∀ t:ο, t ⇒ t = fun x → x
val id : ∀ t:ο, t ⇒ t = fun x → x

val fst : ∀ a:ο, ∀ b:ο, a ⇒ b ⇒ a = fun x y → x

val weird_app : (∀ a:ο, a ⇒ a) ⇒ {} ⇒ {} = fun id x → id x

val pair : ∀ a:ο, ∀ b:ο, a ⇒ b ⇒ {x : a; y : b} = fun x y → {x = x; y = y}
val pfst : ∀ a:ο, ∀ b:ο, {x : a; y : b} ⇒ a = fun p → p.x
val psnd : ∀ a:ο, ∀ b:ο, {x : a; y : b} ⇒ b = fun p → p.y

// Projection of a term
val psnd_trm : ∀ a:ο, ∀ b:ο, {x : a; y : b} ⇒ b = fun p → ((fun x → x) p).y
