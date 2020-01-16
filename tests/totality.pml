
val id : ∀a, a ⇒ a = fun x { x }

type t = [ A ; B ]

val id_t : t ⇒ t = fun x {
  case x { A → A | B → B } }

val a : t = A
val b : t = B

val id_t : t ⇒ t = fun x {
  case x { A → a | B → b } }

def cond⟨x:τ,u:τ,v:τ⟩ = case x { A → u | B → v }

val id_t : t ⇒ t = fun x { cond⟨x,a,b⟩ }

val id_b : bool ⇒ bool = fun x {
  case x { true → true | false → false } }

def cond⟨x,u,v⟩ = case x { true → u | false → v }

val id_b : bool ⇒ bool = fun x { cond⟨x,true,false⟩ }

val f_o_g : ∀a b c, (a ⇒ b) ⇒ (b ⇒ c) ⇒ (a ⇒ c) =
  fun f g x { g (f x) }

//val f_o_g : ∀a b c, (a → b) ⇒ (b ⇒ c) ⇒ (a ⇒ c) =
//  fun f g x { g (f x) }

//val f_o_g : ∀a b c, (a ⇒ b) ⇒ (b → c) ⇒ (a ⇒ c) =
//  fun f g x { g (f x) }

val f_o_g : ∀a b c, (a → b) ⇒ (b → c) ⇒ (a → c) =
  fun f g x { g (f x) }

//val f_o_g : ∀a b c, (a ↝ b) ⇒ (b → c) ⇒ (a → c) =
//  fun f g x { g (f x) }

//val f_o_g : ∀a b c, (a → b) ⇒ (b ↝ c) ⇒ (a → c) =
//  fun f g x { g (f x) }

val f_o_g : ∀a b c, (a ⇏ b) ⇒ (b ⇏ c) ⇒ (a ⇏ c) =
  fun f g x { g (f x) }
