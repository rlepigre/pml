// Booleans

// Type of booleans
def bool : ο = [F of {} ∈ {} ; T of {} ∈ {}]

// Smart constructors
val tru : bool = T[]
val fls : bool = F[]

def eq0 : ι =
  fun b1 b2 →
    case b1 {
      | F[] → case b2 { T[] → fls | F[] → tru }
      | T[] → case b2 { T[] → tru | F[] → fls }
    }

// Equivalence with totality.
val eq : ∀x y∈bool, ∃ v:ι, v ∈ (bool | eq0 x y ≡ v) = eq0

def not0 : ι =
  fun b → case b { F[] → tru | T[] → fls }

val not_total : ∀x∈bool, ∃v:ι, not x ≡ v =
  fun b → case b { F[] → {} | T[] → {} }

val not : bool ⇒ bool = fun b → let x = not_total b in not0 b

//val test0 : ∀x∈bool, not x ≡ not0 x = fun b → {}

val not_idempotent : ∀x∈bool, not (not x) ≡ x = fun b →
  case b { F[] → {} | T[] → {} }

//val test : ∀x∈bool, not (not (not x)) ≡ not x = fun b →
//  let lem0 = not_total b in
//  let lem = not_idempotent (not b) in {}

//val not_total : ∀ x:ι, x∈bool ⇒ ∃ v:ι, not x ≡ v =
//  fun b →
//    case b of
//    | F[x] → {}
//    | T[x] → {}
//
//val or : bool ⇒ bool ⇒ bool =
//  fun b1 b2 →
//    case b1 of
//    | F[x] → b2
//    | T[x] → tru
//
//val or_total : ∀ x:ι, x∈bool ⇒  ∀ y:ι, y∈bool ⇒ ∃ v:ι, or x y ≡ v =
//  fun b1 b2 →
//    case b1 of
//    | F[x] → {}
//    | T[x] → {}
//
//val and : bool ⇒ bool ⇒ bool =
//  fun b1 → fun b2 →
//    case b1 of
//    | F[x] → fls
//    | T[x] → b2
//
//val and_total : ∀ x:ι, x∈bool ⇒  ∀ y:ι, y∈bool ⇒ ∃ v:ι, and x y ≡ v =
//  fun b1 b2 →
//    case b1 of
//    | F[x] → {}
//    | T[x] → {}
//
// Proof of the excluded middle
// val excluded_middle : ∀ x:ι, x∈bool ⇒ or x (not x) ≡ tru =
//  fun b →
//    case b of
//    | F[x] → {}
//    | T[x] → {}
//

// Equivalence is reflexive.
val eq_refl : ∀ x:ι, x∈bool ⇒ eq x x ≡ tru =
  fun b →
    case b {
      | F[x] → {}
      | T[x] → {}
    }

// Equivalence is commutative.
val eq_comm : ∀ x:ι, ∀ y:ι, x∈bool ⇒ y∈bool ⇒ eq x y ≡ eq y x =
  fun b1 b2 →
    case b1 {
      | F[x] → case b2 { T[y] → {} | F[y] → {} }
      | T[x] → case b2 { T[y] → {} | F[y] → {} }
    }

val eq_comm2 : ∀ x:ι, ∀ y:ι, x∈bool ⇒ y∈bool ⇒ eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    case b1 {
      | F[x] → case b2 { T[y] → {} | F[y] → {} }
      | T[x] → case b2 { T[y] → {} | F[y] → {} }
    }

// Equivalence is associative.
val eq_asso : ∀ x:ι, ∀ y:ι, ∀ z:ι, x∈bool ⇒ y∈bool ⇒ z∈bool ⇒
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
//val eq_comm3 : ∀ x:ι, ∀ y:ι, x∈bool ⇒ y∈bool ⇒ eq (eq x y) (eq y x) ≡ tru =
//  fun b1 b2 →
//    let lem1 = eq_comm b1 b2 in
//    let z = eq b1 b2 in
//    let lem2 = eq_refl z in
//    {}
