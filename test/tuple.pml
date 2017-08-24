val fst : ∀x y, x × y ⇒ x =
  fun p { p.1 }

val diag : ∀x, x ⇒ x × x =
  fun x { (x, x) }

val pair : ∀x y, x ⇒ y ⇒ x × y =
  fun x y { (x, y) }

val triple : ∀x y z, x ⇒ y ⇒ z ⇒ x × y × z =
  fun x y z { (x, y, z) }
