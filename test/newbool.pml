// Booleans

type nbool = [T of {} ; F of {}]

// Smart constructors
val tru : nbool = T[{}]
val fls : nbool = F[{}]

// Basic functions.
val eq : nbool ⇒ nbool ⇒ nbool =
  fun b1 b2 →
    case b1 {
      | F[x] → case b2 { T[_] → fls | F[_] → tru }
      | T[x] → case b2 { T[_] → tru | F[_] → fls }
    }

// Equivalence is total.
val eq_total :  ∀ x:ι, x∈nbool ⇒  ∀ y:ι, y∈nbool ⇒ ∃ v:ι, eq x y ≡ v =
  fun b1 b2 →
    case b1 {
      | F[x] → case b2 { T[y] → {} | F[y] → {} }
      | T[x] → case b2 { T[y] → {} | F[y] → {} }
    }

val not : nbool ⇒ nbool =
  fun b →
    case b {
      | F[x] → tru
      | T[x] → fls
    }

val not_total : ∀ x:ι, x∈nbool ⇒ ∃ v:ι, not x ≡ v =
  fun b →
    case b {
      | F[x] → {}
      | T[x] → {}
    }

val or : nbool ⇒ nbool ⇒ nbool =
  fun b1 b2 →
    case b1 {
      | F[x] → b2
      | T[x] → tru
    }

val or_total : ∀ x:ι, x∈nbool ⇒  ∀ y:ι, y∈nbool ⇒ ∃ v:ι, or x y ≡ v =
  fun b1 b2 →
    case b1 {
      | F[x] → {}
      | T[x] → {}
    }

val and : nbool ⇒ nbool ⇒ nbool =
  fun b1 → fun b2 →
    case b1 {
      | F[x] → fls
      | T[x] → b2
    }

val and_total : ∀ x:ι, x∈nbool ⇒  ∀ y:ι, y∈nbool ⇒ ∃ v:ι, and x y ≡ v =
  fun b1 b2 →
    case b1 {
      | F[x] → {}
      | T[x] → {}
    }

// Proof of the excluded middle
val excluded_middle : ∀ x:ι, x∈nbool ⇒ or x (not x) ≡ tru =
  fun b →
    case b {
      | F[x] → {}
      | T[x] → {}
    }

// Equivalence is reflexive.
val eq_refl : ∀ x:ι, x∈nbool ⇒ eq x x ≡ tru =
  fun b →
    case b {
      | F[x] → {}
      | T[x] → {}
    }

// Equivalence is commutative.
val eq_comm : ∀ x:ι, ∀ y:ι, x∈nbool ⇒ y∈nbool ⇒ eq x y ≡ eq y x =
  fun b1 b2 →
    case b1 {
      | F[x] → case b2 { T[y] → {} | F[y] → {} }
      | T[x] → case b2 { T[y] → {} | F[y] → {} }
    }

val eq_comm2 : ∀ x:ι, ∀ y:ι, x∈nbool ⇒ y∈nbool ⇒ eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    case b1 {
      | F[x] → case b2 { T[y] → {} | F[y] → {} }
      | T[x] → case b2 { T[y] → {} | F[y] → {} }
    }

// Equivalence is associative.
val eq_asso : ∀ x:ι, ∀ y:ι, ∀ z:ι, x∈nbool ⇒ y∈nbool ⇒ z∈nbool ⇒
              eq (eq x y) z ≡ eq x (eq y z) =
  fun b1 b2 b3 →
    case b1 {
      | F[x] → case b2 {
                 | T[y] → case b3 { T[z] → {} | F[z] → {} }
                 | F[y] → case b3 { T[z] → {} | F[z] → {} }
               }
      | T[x] → case b2 {
                 | T[y] → case b3 { T[z] → {} | F[z] → {} }
                 | F[y] → case b3 { T[z] → {} | F[z] → {} }
               }
    }

// Other version using "let".
val eq_comm3 : ∀ x:ι, ∀ y:ι, x∈nbool ⇒ y∈nbool ⇒ eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    let lem1 = eq_comm b1 b2 in
    let lem0 = eq_total b1 b2 in
    let lem2 = eq_refl (eq b1 b2) in
    {}
