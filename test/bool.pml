// Booleans

// Type of booleans
def my_bool : ο = [F of {} ; T of {}]

// Smart constructors
val tru : my_bool = T[]
val fls : my_bool = F[]

// Basic functions.
val eq : my_bool ⇒ my_bool ⇒ my_bool =
  fun b1 b2 →
    case b1 {
      | F[_] → case b2 { T[_] → fls | F[_] → tru }
      | T[_] → case b2 { T[_] → tru | F[_] → fls }
    }

val not : my_bool ⇒ my_bool =
  fun b → case b { F[_] → tru | T[_] → fls }

val or : my_bool ⇒ my_bool ⇒ my_bool =
  fun b1 → fun b2 →
    case b1 {
      | F[] → b2
      | T[] → tru
    }

val imp : my_bool ⇒ my_bool ⇒ my_bool =
  fun b1 → fun b2 →
    case b1 {
      | F[] → tru
      | T[] → b2
    }

def land<b1:τ,b2:τ> =
  case b1 {
    | F[] → fls
    | T[] → b2
  }

val and : my_bool ⇒ my_bool ⇒ my_bool =
  fun b1 → fun b2 →
    case b1 {
      | F[] → fls
      | T[] → b2
    }

// Proof of the excluded middle
val excluded_middle : ∀x∈my_bool, or x (not x) ≡ tru =
  fun b →
    case b {
      | F[] → {}
      | T[] → {}
    }

// Equivalence is reflexive.
val eq_refl : ∀x∈my_bool, eq x x ≡ tru =
  fun b →
    case b {
      | F[] → {}
      | T[] → {}
    }

// Equivalence is commutative.
val eq_comm : ∀x y∈my_bool, eq x y ≡ eq y x =
  fun b1 b2 →
    case b1 {
      | F[] → case b2 { T[_] → {} | F[_] → {} }
      | T[] → case b2 { T[_] → {} | F[_] → {} }
    }


val eq_comm2 : ∀x y∈my_bool, eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    case b1 {
      | F[] → case b2 { T[] → {} | F[] → {} }
      | T[] → case b2 { T[] → {} | F[] → {} }
    }

// Equivalence is associative.
val eq_asso : ∀x y z∈my_bool, eq (eq x y) z ≡ eq x (eq y z) =
  fun b1 b2 b3 →
    case b1 {
      | F[] → case b2 {
                | T[] → case b3 { T[_] → {} | F[_] → {} }
                | F[] → case b3 { T[_] → {} | F[_] → {} }
              }
      | T[] → case b2 {
                | T[] → case b3 { T[_] → {} | F[_] → {} }
                | F[] → case b3 { T[_] → {} | F[_] → {} }
              }
    }

// Other version using "let", not correct without proving totality of eq
//val eq_comm3 : ∀x y∈my_bool, eq (eq x y) (eq y x) ≡ tru =
//  fun b1 b2 →
//    let p = eq_comm b1 b2 in
//    let x = eq b1 b2 in
//    let y = eq b2 b1 in
//    eq_refl x

val eq_asso2 : ∀x y z∈my_bool, eq (eq (eq x y) z) (eq x (eq y z)) ≡ tru =
  fun b1 b2 b3 →
    case b1 {
      | F[] → case b2 {
                | T[] → case b3 { T[_] → {} | F[_] → {} }
                | F[] → case b3 { T[_] → {} | F[_] → {} }
              }
      | T[] → case b2 {
                | T[] → case b3 { T[_] → {} | F[_] → {} }
                | F[] → case b3 { T[_] → {} | F[_] → {} }
              }
    }
