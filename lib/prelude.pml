type unit = {}

type bool = [Tru ; Fls]

val tru : bool = Tru[]
val fls : bool = Fls[]

def if<c:τ,t:τ,e:τ> : τ =
  case c of
  | Tru[] → t
  | Fls[] → e

val and : bool ⇒ bool ⇒ bool = fun a b → if<a, b, fls>

val or  : bool ⇒ bool ⇒ bool = fun a b → if<a, tru, b>
