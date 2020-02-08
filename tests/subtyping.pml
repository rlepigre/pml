// test subtyping with variable parameter
type rec ml⟨c⟩ = [ N; C of c × ml⟨c×c⟩ ]

val test : ∀s,∀c, ml^s⟨c⟩ ⇒ ml⟨c⟩ = fun x { x }

type t1 = [ A ]
type t2 = [ A ; B ]

assert t1 ⊂ t2

//assert ml⟨t1⟩ ⊂ ml⟨t2⟩ //still fails: generalisation is needed,
                         //but with only one parameter.

// and bound parameters
type sub⟨a,c⟩ = (∀x:ο→ο, c⟨x⟩ → a⟨x⟩)

type rec ccc⟨c⟩=
  [ S of ∃x:ο, c⟨x⟩
  ; U of ∃cs:(ο→ο)→ο, sub⟨ccc,cs⟩]

val test : ∀s,∀c, ccc^s⟨c⟩ ⇒ ccc⟨c⟩ = fun x { x }

type t1⟨x⟩ = [ A of x ; D ]
type t2⟨x⟩ = [ A of x ; B of x × x ; C ; D]

//assert ccc⟨t1⟩ ⊂ ccc⟨t2⟩ //still fails, same as above
