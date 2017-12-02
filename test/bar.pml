
include lib.nat
include lib.list

// la implication intuitioniste est incluse dans la implication classique
val test1 : ∀a b, (a ⇒ b) ⇒ (a → b) = fun f { f }

// la implication classique s'envoie sur a ⇒ non non b
val test2 : ∀a b, (a → b) ⇒ (a ⇒ (b ⇒ ∀x,x) ⇒ ∀x,x) =
   fun f x g { delim { (g (f x)) } }


// paire dependante
type dep_pair⟨k,v:τ→ο⟩ = ∃x:τ,x∈k * v⟨x⟩

// map avec paire dépandantes
type map⟨k,v⟩ = list⟨dep_pair⟨k,v⟩⟩

val add : ∀k,∀v:τ→ο, ∀x∈k, v⟨x⟩ ⇒ map⟨k,v⟩ ⇒ map⟨k,v⟩ = fun k v m { (k,v) :: m }

// type d'une égalité, quand c'est vrai, c'est égal!
type eq⟨k⟩ = ∀x∈k, ∀y∈k, [ true of x ≡ y ; false of x ≠ y ]

val test3 : ∀k, eq⟨k⟩ ⇒ (k ⇒ k ⇒ bool) = fun x { x }

val rec assoc : ∀k,∀v:τ→ο, eq⟨k⟩ ⇒ ∀x∈k, map⟨k,v⟩ ⇒ option⟨v⟨x⟩⟩ =
  fun cmp x l {
    let k such that cmp : eq⟨k⟩;
    case l {
      []   → None
      c::l → let (y,v) = c;
             if cmp x y { Some[v] } else
               { assoc cmp (x:k) l }
    }
  }

// La bar recursion ⋯ qui ne passe pas le test de terminaison.
// Mais ça type !!!

// notes
// → : implication classique
// ⇒ : implication intuitionniste
// delim : pour (si on a le droit) passer de classique à inuitionniste,
//         on a le droit si le but est de type bottom. Mais aussi si
//         il n'y a aucune implication classique dans le séquant.
val unsafe bar_aux : ∀a,∀v:τ→ο, ∀m∈map⟨a,v⟩, eq⟨a⟩ ⇒ (∀x, x∈a → v⟨x⟩) → ∀x, x∈a ⇒ v⟨x⟩ =
  fun m cmp f { save st { fun x {
        let a such that cmp : eq⟨a⟩;
        //let v such that _ : v⟨x⟩; ne marche pas mais devrait !
        case assoc cmp (x:a) m {
          Some[v] → v
          None    → (delim {
              let u = f x;
              let m = add (x:a) u m;
              restore st (bar_aux m cmp f) } : ∀x,x)
        }
      }}}

val bar : ∀a,∀v:τ→ο, eq⟨a⟩ ⇒ (∀x, x∈a → v⟨x⟩) → ∀x, x∈a ⇒ v⟨x⟩ =
  fun cmp f { bar_aux [] cmp f }

// Axiome du choix intuitionniste On voudrait
val aci : ∀a,∀v, (∀x∈a, v⟨x⟩) ⇒ ∃f,∀x∈a, (f x)∈v⟨x⟩ =
  fun f {
    let a, v such that f : ∀x∈a, v⟨x⟩;
    (fun x { let u = (f x : v⟨x⟩); u } : ∀x∈a, (f x)∈v⟨x⟩)
  }

// On voudrait vraiment ça:
// val aci : ∀a,∀v, (∀x∈a, ∃y, v⟨x,y⟩) ⇒ ∃f,∀x∈a, v⟨x, f⟨x⟩⟩ =
// Mais il faudrait des liaisons dans les epsilons (au moins les ewit)

// La version classique ne marche, fort heureusement,
// grâce à la value restriction.
// val acc : ∀a,∀v, (∀x, x∈a → v⟨x⟩) → ∃f,∀x, x∈a → (f x)∈v⟨x⟩ =
//   fun f {
//     let a, v such that f : ∀x∈a, v⟨x⟩;
//     (fun x { let u = (f x : v⟨x⟩); u } : ∀x∈a, (f x)∈v⟨x⟩)
//   }

// Et l'axiome du choix dénombrable et classique.
val acc_den : ∀a,∀v:τ→ο, eq⟨a⟩ ⇒ (∀x, x∈a → v⟨x⟩) → ∃f,∀x∈a, (f x)∈v⟨x⟩ =
  fun cmp f { aci (bar cmp f) }
