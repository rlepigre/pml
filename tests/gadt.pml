include lib.nat
include lib.bool

type rec ty⟨a:ο⟩ = [ N of nat × (a ⊂ nat) × (nat ⊂ a)
                 ; B of bool × (a ⊂ bool) × (bool ⊂ a)
                 ; F of ∃b c:ο, (b ⇒ ty⟨c⟩) × (a ⊂ (b ⇒ c)) × ((b ⇒ c) ⊂ a)
                 ; A of ∃b:ο, ty⟨b⇒a⟩ × ty⟨b⟩
                 ; P of ∃b c:ο, ty⟨b⟩ × ty⟨c⟩ × (a ⊂ (b × c)) × ((b × c) ⊂ a)
                 ; P1 of ∃c, ty⟨a × c⟩
                 ; P2 of ∃c, ty⟨c × a⟩
                 ]

val id : ∀a, a ⇒ a = fun x { x }

val n : nat ⇒ ty⟨nat⟩ = fun x {N[(x, id, id)]}

val b : bool ⇒ ty⟨bool⟩ = fun x {B[(x, id, id)]}

val f : ∀a b, (a ⇒ ty⟨b⟩) ⇒ ty⟨a ⇒ b⟩ =
  fun x { F[(x, id, id)]}

val a : ∀a b, ty⟨a ⇒ b⟩ ⇒ ty⟨a⟩ ⇒ ty⟨b⟩ =
  fun x y { A[(x, y)]}

val p : ∀a b, ty⟨a⟩ ⇒ ty⟨b⟩ ⇒ ty⟨a × b⟩ =
  fun x y { P[(x, y, id, id)]}

val p1 : ∀a b, ty⟨a×b⟩ ⇒ ty⟨a⟩ =
  fun x { P1[x] }

val p2 : ∀a b, ty⟨a×b⟩ ⇒ ty⟨b⟩ =
  fun x { P2[x] }

val rec get : ∀a, ty⟨a⟩ ⇒ a = fun x {
  case x {
     N[(x,s,s')] → check s' x for x
     B[(x,s,s')] → check s' x for x
     F[(x,s,s')] → let f = fun y { get (x y) }; check s' f for f
     A[(x,y)]    → get x (get y)
     P[(x,y,s,s')] → let p = (get x, get y); check s' p for p
     P1[x]        → (get x).1
     P2[x]        → (get x).2
  }}

// same as above with some contradiction, but we still need the
// above get to do an eta-expansion and get the contradiction
// but the compiler would know that these cases are impossible
val get_n : ty⟨nat⟩ ⇒ nat = fun x {
  case x {
    N[(x,s,s')] → x
    B[(x,s,s')] → let y = check s' true for true; ✂
    F[(x,s,s')] → let f = fun z {get (x z)}; let y = check s' f for f; ✂
    P[(x,y,s,s')] → let p = (get x, get y); let y = check s' p for p; ✂
    A[(x,y)] → get x (get y)
    P1[x] → (get x).1
    P2[x] → (get x).2
  }}

val idt_nat: ty⟨nat ⇒ nat⟩ = f (fun x {n x})
val z: ty⟨nat⟩ = a idt_nat (n 0)
val z: nat = get z