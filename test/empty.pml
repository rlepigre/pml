val e1 : (∀ x:ο, x) ⇒ [] = λx.x
val e2 : [] ⇒ (∀ x:ο, x) = λx.case x { }
