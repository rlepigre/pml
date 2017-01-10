// Option type
def option (a : ο) : ο = [None of {} ; Some of a]

// Smart constructors
val none : ∀ (a : ο) option<a> = None[]
val some : ∀ (a : ο) a ⇒ option<a> = λx.Some[x]

val map : ∀ (a : ο) ∀ (b : ο) (a ⇒ b) ⇒ option<a> ⇒ option<b> =
  fun f eo →
    case eo of
    | None[x] → None[x]
    | Some[e] → (λx.Some[x]) (f e)

//val map : ∀ (a : ο) ∀ (b : ο) (a ⇒ b) ⇒ option<a> ⇒ option<b> =
//  fun f eo →
//    case eo of
//    | None[x] → None[x]
//    | Some[e] → some (f e)
