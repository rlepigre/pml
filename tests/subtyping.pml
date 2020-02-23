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

include lib.nat

type corec list⟨a⟩ = { head:a; tail:list⟨a⟩ }
type corec natlist = { head:nat; tail:natlist }

assert natlist  ⊂ list⟨nat⟩
assert list⟨nat⟩  ⊂ natlist

type corec any_expl⟨a⟩ = { head:a; explode:any_expl⟨any_expl⟨a⟩⟩ }
type nat_expl = { head:nat; explode:any_expl⟨any_expl⟨nat⟩⟩ }

assert any_expl⟨nat⟩ ⊂ nat_expl
assert nat_expl ⊂ any_expl⟨nat⟩

//set log "s"
//assert any_expl⟨any_expl⟨nat⟩⟩ ⊂ any_expl⟨nat_expl⟩
//assert any_expl⟨nat_expl⟩ ⊂ any_expl⟨any_expl⟨nat⟩⟩
//assert { head : nat ; explode : any_expl⟨nat_expl⟩ } ⊂ { head : nat ; explode : any_expl⟨any_expl⟨nat⟩⟩ ; ⋯ }
//assert { head : nat ; explode : any_expl⟨any_expl⟨nat_expl⟩⟩ } ⊂ { head : nat ; explode : any_expl⟨any_expl⟨any_expl⟨nat⟩⟩⟩; ⋯ }

type corec nat_expl2⟨s⟩ = μ_s nat_expl, { head:nat; explode:any_expl^s⟨nat_expl⟩ }

//assert any_expl⟨nat⟩ ⊂ nat_expl2⟨∞⟩
