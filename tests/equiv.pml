val refl1 : {} ≡ {} = {}
val refl2 : (fun x { x }) ≡ (fun x { x }) = {}
val refl3 : C[{}] ≡ C[{}] = {}

val refl_v : ∀ x:ι, x ≡ x = {}
val refl_t : ∀ a:τ, a ≡ a = {}

val symm_v : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ y ≡ x = fun x { {} }
val symm_t : ∀ a:τ, ∀ b:τ, a ≡ b ⇒ b ≡ a = fun x { {} }

val symm_v2 : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ y ≡ x = fun x { x }
val symm_t2 : ∀ a:τ, ∀ b:τ, a ≡ b ⇒ b ≡ a = fun x { x }

val tran_v : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = fun x y { {} }
val tran_t : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = fun x y { {} }

val tran_v2 : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = fun x y { x }
val tran_t2 : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = fun x y { x }
val tran_v3 : ∀ x:ι, ∀ y:ι, ∀ z:ι, x ≡ y ⇒ y ≡ z ⇒ x ≡ z = fun x y { y }
val tran_t3 : ∀ a:τ, ∀ b:τ, ∀ c:τ, a ≡ b ⇒ b ≡ c ⇒ a ≡ c = fun x y { y }

val cons_neq : ∀ x:ι, ∀ y:ι, C[x] ≠ D[y] = {}

val cons_eq  : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ C[x] ≡ C[y] = fun x { {} }
val cons_eq2 : ∀ x:ι, ∀ y:ι, x ≡ y ⇒ C[x] ≡ C[y] = fun x { x }

val id_eq : ∀ y:ι, ((fun x { x }) y) ≡ y = {}

def comp⟨f,g⟩ = fun x { f (g x) }

// from here we study a form of axiom of choice that could be usefull ⋯

type top = ∃x, x
type bot = ∀x, x

def id = fun x { x }

// remark, a could be bottom and b top, i.e. the type of all function
// this axiom will need to assume f and g are not record if we allow
// default field in record (not just as a syntactic sugar).
// this is a form of axiom of choice!
// using a↝b means that function can have effect of even not terminate
val eq_fun_axiom : ∀a b, ∀f g∈a↛b, f≠g ⇒ ∃x∈top, f x ≠ g x = {--}

val comp_assoc : ∀a b c d, ∀f∈c↛d, ∀g∈b↛c, ∀h∈a↛b,
                   comp⟨f,comp⟨g,h⟩⟩ ≡ comp⟨comp⟨f, g⟩, h⟩ =
  fun f g h {
    eq_fun_axiom comp⟨f,comp⟨g,h⟩⟩ comp⟨comp⟨f, g⟩, h⟩ {}
  }

val comp_neut_right : ∀a b, ∀f ∈ a ↛ b, comp⟨f, id⟩ ≡ f =
  fun f {
    eq_fun_axiom comp⟨f,id⟩ f {}
  }

val comp_neut_left : ∀a b, ∀f ∈ a ↛ b, comp⟨id, f⟩ ≡ f =
  fun f {
    eq_fun_axiom comp⟨id,f⟩ f {}
  }

include lib.nat

val rec id_nat : nat ⇒ nat = fun n {
  case n {
    Zero → Zero
    S[p] → S[id_nat p]
  }
}

val equiv_nat
  : ∀a, ∀f g∈ nat ⇒ a, comp⟨f,id_nat⟩ ≠ comp⟨g,id_nat⟩ ⇒ ∃n∈nat, f n ≠ g n
  = fun f g p {
    let (x,q) = eq_fun_axiom comp⟨f,id_nat⟩ comp⟨g,id_nat⟩ p;
    let lem : x ≠ Zero ⇒ (∀v:ι, x ≠ S[v]) ⇒ bot =
      fun z s { {--} };
    {--}
  }