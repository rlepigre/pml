val e1 : (∀ x:ο, x) ⇒ ∅ = fun x { x }
val e2 : ∅ ⇒ (∀ x:ο, x) = fun x { case x { } }
