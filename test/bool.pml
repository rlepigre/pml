// Booleans

// Type of booleans
def bool : ο = [F of {} ; T of {}]

// Smart constructors
val tru : bool = T[]
val fls : bool = F[]

// Basic functions.
val eq : bool ⇒ bool ⇒ bool =
  fun b1 b2 →
    case b1 of
    | F[] → (case b2 of
              | T[] → fls
              | F[] → tru)
    | T[] → (case b2 of
              | T[] → tru
              | F[] → fls)

val not : bool ⇒ bool =
  fun b →
    case b of
    | F[] → tru
    | T[] → fls

val or : bool ⇒ bool ⇒ bool =
  fun b1 → fun b2 →
    case b1 of
    | F[] → b2
    | T[] → tru

val and : bool ⇒ bool ⇒ bool =
  fun b1 → fun b2 →
    case b1 of
    | F[] → fls
    | T[] → b2

// Proof of the excluded middle
val excluded_middle : ∀x∈bool, or x (not x) ≡ tru =
  fun b →
    case b of
    | F[] → {}
    | T[] → {}

// Equivalence is reflexive.
val eq_refl : ∀x∈bool, eq x x ≡ tru =
  fun b →
    case b of
    | F[] → {}
    | T[] → {}

// Equivalence is commutative.
val eq_comm : ∀x y∈bool, eq x y ≡ eq y x =
  fun b1 b2 →
    case b1 of
    | F[] → (case b2 of | T[y] → {} | F[y] → {})
    | T[] → (case b2 of | T[y] → {} | F[y] → {})


val eq_comm2 : ∀x y∈bool, eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    case b1 of
    | F[] → (case b2 of | T[] → {} | F[] → {})
    | T[] → (case b2 of | T[] → {} | F[] → {})

// Equivalence is associative.
val eq_asso : ∀x y z∈bool, eq (eq x y) z ≡ eq x (eq y z) =
  fun b1 b2 b3 →
    case b1 of
    | F[] → (case b2 of
              | T[] → (case b3 of | T[z] → {} | F[z] → {})
              | F[] → (case b3 of | T[z] → {} | F[z] → {}))
    | T[] → (case b2 of
              | T[] → (case b3 of | T[z] → {} | F[z] → {})
              | F[] → (case b3 of | T[z] → {} | F[z] → {}))

// Other version using "let", not correct without proving totality of eq
//val eq_comm3 : ∀x y∈bool, eq (eq x y) (eq y x) ≡ tru =
//  fun b1 b2 →
//    let p = eq_comm b1 b2 in
//    let x = eq b1 b2 in
//    let y = eq b2 b1 in
//    eq_refl x

val eq_asso2 : ∀x y z∈bool, eq (eq (eq x y) z) (eq x (eq y z)) ≡ tru =
  fun b1 b2 b3 →
    case b1 of
    | F[] → (case b2 of
              | T[] → (case b3 of | T[z] → {} | F[z] → {})
              | F[] → (case b3 of | T[z] → {} | F[z] → {}))
    | T[] → (case b2 of
              | T[] → (case b3 of | T[z] → {} | F[z] → {})
              | F[] → (case b3 of | T[z] → {} | F[z] → {}))
