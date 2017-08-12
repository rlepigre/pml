// Option type
def option<a:ο> : ο = [None of {} ; Some of a]

// Smart constructors
val none : ∀ a:ο, option<a> = None[]
val some : ∀ a:ο, a ⇒ option<a> = fun x → Some[x]

val map : ∀ a:ο, ∀ b:ο, (a ⇒ b) ⇒ option<a> ⇒ option<b> =
  fun f eo →
    case eo {
      | None[x] → None[x]
      | Some[e] → (fun x → Some[x]) (f e)
    }


val map : ∀ a:ο, ∀ b:ο, (a ⇒ b) ⇒ option<a> ⇒ option<b> =
  fun f eo →
    case eo {
      | None[x] → none
      | Some[e] → some (f e)
    }

val from_opt : ∀ a:ο, option<a> ⇒ a ⇒ a =
  fun eo d →
    case eo {
      | None[x] → d
      | Some[v] → v
    }

def total<f:ι,a:ο> : ο = ∀x:ι, x∈a ⇒ ∃v:ι, f x ≡ v

val map_map : ∀ a b c:ο, ∀f∈(a⇒b), ∀g∈(b⇒c), ∀o∈option<a>, total<f,a> ⇒
    map g (map f o) ≡ map (fun x → g (f x)) o =
  fun f1 f2 eo h →
    case eo {
      | None[y] → {}
      | Some[e] → let lem = h e in {}
    }

// FIXME ne peux pas marcher si f (et g ?) n'est pas totale.
//val map_map : ∀ a b c:ο, ∀ f g o:ι, f∈(a⇒b) ⇒ g∈(b⇒c) ⇒ o∈option<a> ⇒
//    map g (map f o) ≡ map (fun x → g (f x)) o = fun f1 f2 eo →
//  case eo {
//    | None[y] → {}
//    | Some[e] → {}
//  }
