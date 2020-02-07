// test subtyping with variable parameter
type rec ml⟨c⟩ = [ N; C of c × ml⟨c×c⟩ ]

val test : ∀s,∀c, ml^s⟨c⟩ ⇒ ml⟨c⟩ = fun x { x }

// and bound parameters
type sub⟨a,c⟩ = (∀x:ι→ο, c⟨x⟩ → a⟨x⟩)

type rec ccc⟨c⟩=
  [ S of ∃x:ι, c⟨x⟩
  ; U of ∃cs, sub⟨ccc,cs⟩]

val test : ∀s,∀c, ccc^s⟨c⟩ ⇒ ccc⟨c⟩ = fun x { x }