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
val is_Gs : cmp ⇒ bool =
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
