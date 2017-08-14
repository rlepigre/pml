def delta : ι         = fun x { x x }
def app<t:τ, u:τ> : τ = t u
def omega : τ         = app<delta, delta>
def neg<a:ο> : ο      = a ⇒ ∀x:ο, x
type boolean = [T ; F] 
def boolean : ο = [T ; F]
def list<a:ο> : ο = μ list [ Nil ; Cons of { hd : a ; tl : list } ]
type rec list<a:ο> = [ Nil ; Cons of { hd : a ; tl : list } ]
val is_empty : ∀a:ο, list<a> ⇒ boolean =
  fun l { case l { Nil[_] → T | Cons[_] → F } }

val rec last : ∀a:ο, list<a> ⇒ [None ; Some of a] =
  fun l {
    case l {
      Nil[_]  → None
      Cons[c] → case c.tl {
                  Nil[_]  → Some[c.hd]
                  Cons[_] → last c.tl
                }
    }
  }
