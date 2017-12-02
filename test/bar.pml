
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
type eq⟨k⟩ = ∀x∈k, ∀y∈k, [ true of x ≡ y ; false ]

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
val unsafe bar_aux : ∀k,∀v:τ→ο, ∀m∈map⟨k,v⟩, eq⟨k⟩ ⇒ (∀x, x∈k → v⟨x⟩) → ∀x, x∈k ⇒ v⟨x⟩ =
  fun m cmp f { save a { fun x {
        let k such that cmp : eq⟨k⟩;
        //let v such that _ : v⟨x⟩; ne marche pas mais devrait !
        case assoc cmp (x:k) m {
          Some[v] → v
          None    → (delim {
              let u = f x;
              let m = add (x:k) u m;
              restore a (bar_aux m cmp f) } : ∀x,x)
        }
      }}}

val bar : ∀k,∀v:τ→ο, eq⟨k⟩ ⇒ (∀x, x∈k → v⟨x⟩) → ∀x, x∈k ⇒ v⟨x⟩ =
  fun cmp f { bar_aux [] cmp f }
