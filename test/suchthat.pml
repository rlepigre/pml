val id : ∀a, a ⇒ a =
  fun x {
    let a such that x : a in (x : a)
  }

// Should not work
//val id : ∀a, a ⇒ a =
//  fun x {
//    let a such that x : {} in (x : a)
//  }
