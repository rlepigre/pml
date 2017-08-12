// Commutations of quantifiers

// Mitchell's containment axiom is not classically provable.
// val m : ∀ a b:ο→ο, (∀ x:ο, a<x> ⇒ b<x>) ⇒ ((∀ x:ο, a<x>) ⇒ (∀ x:ο, b<x>)) =
//   fun f → f

// A variant of Mitchell's containment axiom.
val c1 : ∀ a b:ο→ο, (∀ x:ο, a<x> ⇒ b<x>) ⇒ ((∃ x:ο, a<x>) ⇒ (∃ x:ο, b<x>)) =
  fun f → f

// Commutation of quantifiers.
val uu : ∀ a:ο→ο→ο, (∀ x y:ο, a<x,y>) ⇒ (∀ x y:ο, a<y,x>) = fun x → x
val ee : ∀ a:ο→ο→ο, (∃ x y:ο, a<x,y>) ⇒ (∃ x y:ο, a<y,x>) = fun x → x
val eu : ∀ a:ο→ο→ο, (∃ x:ο, ∀ y:ο, a<x,y>) ⇒ (∀ y:ο, ∃ x:ο, a<x,y>) =
  fun x → x

// Invalid.
// val ue : ∀ a:ο→ο→ο, (∀ x:ο, ∃ y:ο, a<x,y>) ⇒ (∃ y:ο, ∀ x:ο, a<x,y>) =
//   fun x → x

// Invalid.
// val pr : ∀ a b:ο→ο, (∀ x:ο, {l : a<x>; r : b<x>})
//        ⇒ {l : ∀ x:ο, a<x>; r : ∀ x:ο, b<x>} =
//   fun x → x

val pr : ∀ a b:ο→ο, {l : ∀ x:ο, a<x>; r : ∀ x:ο, b<x>}
       ⇒ (∀ x:ο, {l : a<x>; r : b<x>}) =
  fun x → x

// Invalid.
// val sm : ∀ a b:ο→ο, (∀ x:ο, [L of a<x> ; R of b<x>])
//        ⇒ [L of ∀ x:ο, a<x>; R of ∀ x:ο, b<x>]
//   fun x → x

val sm : ∀ a b:ο→ο, [L of ∀ x:ο, a<x>; R of ∀ x:ο, b<x>]
       ⇒ (∀ x:ο, [L of a<x> ; R of b<x>])
  = fun x → x
