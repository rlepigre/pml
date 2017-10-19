def stream<a:ο> : ο = νx, {} ⇒ { hd : a; tl : x }

val hd : ∀a:ο, stream<a> ⇒ a         = fun s { (s {}).hd }
val tl : ∀a:ο, stream<a> ⇒ stream<a> = fun s { (s {}).tl }
