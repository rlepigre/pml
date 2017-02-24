def list<a:ο> : ο = μx [ Nil of {} ; Cns of { hd : a; tl : x } ]

val nil : ∀a:ο, list<a> = Nil[{}]
val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l → Cns[{ hd = e; tl = l }]
