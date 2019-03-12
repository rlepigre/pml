// Option type
def option⟨a:ο⟩ : ο = [None of {} ; Some of a]

// Smart constructors
val none : ∀ a:ο, option⟨a⟩ = None
val some : ∀ a:ο, a ⇒ option⟨a⟩ = fun x { Some[x] }

val map : ∀ a:ο, ∀ b:ο, (a ⇒ b) ⇒ option⟨a⟩ ⇒ option⟨b⟩ =
  fun f eo {
    case eo {
      None[x] → None[x]
      Some[e] → Some[f e]
    }
  }


val map : ∀ a:ο, ∀ b:ο, (a ⇒ b) ⇒ option⟨a⟩ ⇒ option⟨b⟩ =
  fun f eo {
    case eo {
      | None[x] → none
      | Some[e] → some (f e)
    }
  }

val from_opt : ∀ a:ο, option⟨a⟩ ⇒ a ⇒ a =
  fun eo d {
    case eo {
      None[x] → d
      Some[v] → v
    }
  }

val map_map : ∀ a b c:ο, ∀f∈(a⇒b), ∀g∈(b⇒c), ∀o∈option⟨a⟩,
              map g (map f o) ≡ map (fun x { g (f x) }) o =
  fun f g eo {
    case eo {
      None[y] → {}
      Some[e] → {}
    }
  }
