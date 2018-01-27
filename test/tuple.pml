val fst : ∀x y, x × y ⇒ x =
  fun p { p.1 }

val diag : ∀x, x ⇒ x × x =
  fun x { (x, x) }

val pair : ∀x y, x ⇒ y ⇒ x × y =
  fun x y { (x, y) }

val triple : ∀x y z, x ⇒ y ⇒ z ⇒ x × y × z =
  fun x y z { (x, y, z) }

val curry : ∀x y z, (x ⇒ y ⇒ z) ⇒ x × y ⇒ z =
  fun f c {
    let (x,y) = c;
    f x y
  }

type rec list⟨a⟩ = [Nil ; Cons of a × list]

val rec map : ∀a b, (a ⇒ b) ⇒ list⟨a⟩ ⇒ list⟨b⟩ =
  fun f l {
    case l {
      Nil          → Nil
      Cons[(x, l)] → Cons[(f x, map f l)]
    }
  }
