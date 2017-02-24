
def nat : ο = μx [ Z of {} ; S of x ]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

def list<a:ο> : ο = μx [ Nil of {} ; Cns of { hd : a; tl : x } ]

val nil : ∀a:ο, list<a> = Nil[{}]
val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l → Cns[{ hd = e; tl = l }]

def stream<a:ο> : ο = νx {} ⇒ { hd : a; tl : x }

val hd : ∀a:ο, stream<a> ⇒ a         = fun s → (s {}).hd
val tl : ∀a:ο, stream<a> ⇒ stream<a> = fun s → (s {}).tl
