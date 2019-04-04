include lib.option
include lib.nat
include lib.list

// la implication intuitioniste est incluse dans la implication classique
val test1 : ∀a b, (a ⇒ b) ⇒ (a → b) = fun f { f }

// paire dependante
type dep_pair⟨k,v:τ→ο⟩ = ∃x:τ,x∈k × v⟨x⟩

// map avec paire dépandantes
type map⟨k,v⟩ = list⟨dep_pair⟨k,v⟩⟩

val add : ∀k,∀v:τ→ο, ∀x∈k, v⟨x⟩ ⇒ map⟨k,v⟩ ⇒ map⟨k,v⟩ = fun k v m { (k,v) :: m }

// type d'une égalité, quand c'est vrai, c'est égal!
type eq⟨k⟩ = ∀x∈k, ∀y∈k, [ true of x ≡ y ; false of x ≠ y ]

val test3 : ∀k, eq⟨k⟩ ⇒ (k ⇒ k ⇒ bool) = fun x { x }

val rec assoc : ∀k,∀v:τ→ο, eq⟨k⟩ ⇒ ∀x∈k, map⟨k,v⟩ ⇒ option⟨v⟨x⟩⟩ =
  fun cmp x l {
    case l {
      []   → None
      c::l → let (y,v) = c;
             if cmp x y { Some[v] } else
               { assoc cmp x l }
    }
  }

// La bar recursion ⋯ qui ne passe pas le test de terminaison.
// Mais ça type !!!

def neg⟨a⟩ = a →_(l) ∀x,x

// notes
// → : implication classique
// ⇒ : implication intuitionniste
// →_(l) : implication non terminante
val rec bar_aux : ∀a,∀v:τ→ο, ∀m∈map⟨a,v⟩, eq⟨a⟩ ⇒ (∀x∈a, neg⟨neg⟨v⟨x⟩⟩⟩) ⇒ neg⟨neg⟨∀x, x∈a →_(l) v⟨x⟩⟩⟩ =
  fun m cmp f g {
    let a,v such that m : map⟨a,v⟩;
    g (fun x {
        case assoc cmp x m {
          Some[v] → v
          None    →
            f x (fun u {
                let m = add x u m;
                bar_aux m cmp f g })}
      } : ∀x, x∈a →_(l) v⟨x⟩)}

val bar : ∀a,∀v:τ→ο, eq⟨a⟩ ⇒ (∀x∈a, neg⟨neg⟨v⟨x⟩⟩⟩) ⇒ neg⟨neg⟨∀x, x∈a →_(l) v⟨x⟩⟩⟩ =
  fun cmp f g { bar_aux [] cmp f g }

// Axiome du choix intuitionniste On voudrait
val aci : ∀a,∀v, (∀x∈a, v⟨x⟩) ⇒ ∃f,∀x∈a, (f x)∈v⟨x⟩ =
  fun f {
    let a, v such that f : ∀x∈a, v⟨x⟩;
    (fun x { let u = (f x : v⟨x⟩); u } : ∀x∈a, (f x)∈v⟨x⟩)
  }

// On voudrait vraiment ça:
// val aci : ∀a,∀v, (∀x∈a, ∃y, v⟨x,y⟩) ⇒ ∃f,∀x∈a, v⟨x, f⟨x⟩⟩ =
// Mais il faudrait des liaisons dans les epsilons (au moins les ewit)

val aci2 : ∀a,∀v, (∀x, x∈a →_(l) v⟨x⟩) ⇒ ∃f,∀x, x∈a →_(l) (f x)∈v⟨x⟩ =
  fun f {
   let a, v such that f : ∀x, x∈a →_(l) v⟨x⟩;
   (fun x { let u = (f x : v⟨x⟩); u } : ∀x, x∈a →_(l) (f x)∈v⟨x⟩)
  }

// La version classique ne marche pas, fort heureusement,
// grâce à la value restriction.
// val acc : ∀a,∀v, (∀x, x∈a → v⟨x⟩) → ∃f,∀x, x∈a → (f x)∈v⟨x⟩ =
//   fun f {
//     let a, v such that f : ∀x∈a, v⟨x⟩;
//     (fun x { let u = (f x : v⟨x⟩); u } : ∀x∈a, (f x)∈v⟨x⟩)
//   }

// Et l'axiome du choix dénombrable et classique a besoin de aci2
val acc_den : ∀a,∀v:τ→ο, eq⟨a⟩ ⇒ (∀x∈a, neg⟨neg⟨v⟨x⟩⟩⟩) ⇒ neg⟨neg⟨∃f,∀x, x∈a →_(l) (f x)∈v⟨x⟩⟩⟩ =
  fun cmp f g { bar cmp f (fun h { g (aci2 h) }) }
