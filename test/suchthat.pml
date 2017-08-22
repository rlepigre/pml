val id : ∀a, a ⇒ a =
  fun x {
    let a such that x : a in (x : a)
  }

// Should not work
//val id : ∀a, a ⇒ a =
//  fun x {
//    let a such that x : {} in (x : a)
//  }


val app : ∀a b, (a ⇒ b) ⇒ a ⇒ b =
  fun f x {
    let a, b such that f : a ⇒ b in ((f (x : a)) : b)
  }
