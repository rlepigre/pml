type cmp = [Ls ; Eq ; Gr]
type cmp' = [Ls ; Eq ; Gr; Bot]

val is_Ls : cmp ⇒ bool =
  fun x { case x { Ls → true  | Eq → false | Gr → false } }
val is_Le : cmp ⇒ bool =
  fun x { case x { Ls → true  | Eq → true  | Gr → false } }
val is_Eq : cmp ⇒ bool =
  fun x { case x { Ls → false | Eq → true  | Gr → false } }
val is_Ge : cmp ⇒ bool =
  fun x { case x { Ls → false | Eq → true  | Gr → true  } }
val is_Gr : cmp ⇒ bool =
  fun x { case x { Ls → false | Eq → false | Gr → true  } }

val compose : cmp ⇒ cmp ⇒ cmp' = fun c1 c2 {
  case c1 {
    Ls → case c2 {
      Ls → Ls
      Eq → Ls
      Gr → Bot
    }
    Eq → c2
    Gr → case c2 {
      Ls → Bot
      Eq → Gr
      Gr → Gr
    }
  }
}

val inverse : cmp ⇒ cmp = fun c {
  case c {
    Ls → Gr
    Eq → Eq
    Gr → Ls
  }
}

type dcmp⟨a,b⟩ = [Ls ; Eq of a ≡ b ; Gr]

type rel⟨a⟩ = ∃f,
 { f     : f ∈ (a ⇒ a ⇒ cmp)
 ; sym   : ∀x y∈a, f y x ≡ inverse (f x y)
 ; ⋯}

type preorder⟨a⟩ = ∃f,
  { f     : f ∈ (a ⇒ a ⇒ cmp)
  ; sym   : ∀x y∈a, f y x ≡ inverse (f x y)
  ; refl  : ∀x∈a, f x x ≡ Eq
  ; trans : ∀x y z∈a, f x z ≡ compose (f x y) (f y z)
  ; ⋯ }

type order⟨a⟩ = ∃f,
  { f     : f ∈ (a ⇒ a ⇒ cmp)
  ; sym   : ∀x y∈a, f y x ≡ inverse (f x y)
  ; refl  : ∀x∈a, f x x
  ; trans : ∀x y z∈a, f x z ≡ compose (f x y) (f y z)
  ; anti  : ∀x y∈a, f x y ≡ Eq ⇒ x ≡ y
  ; ⋯ }
