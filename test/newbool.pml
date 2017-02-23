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
    | F[x] → (case b2 of
              | T[y] → fls
              | F[y] → tru)
    | T[x] → (case b2 of
              | T[y] → tru
              | F[y] → fls)

// Equivalence is total.
val eq_total :  ∀ x:ι, x∈bool ⇒  ∀ y:ι, y∈bool ⇒ ∃ v:ι, eq x y ≡ v =
  fun b1 b2 →
    case b1 of
    | F[x] → (case b2 of | T[y] → {} | F[y] → {})
    | T[x] → (case b2 of | T[y] → {} | F[y] → {})

val not : bool ⇒ bool =
  fun b →
    case b of
    | F[x] → tru
    | T[x] → fls

val not_total : ∀ x:ι, x∈bool ⇒ ∃ v:ι, not x ≡ v =
  fun b →
    case b of
    | F[x] → {}
    | T[x] → {}

val or : bool ⇒ bool ⇒ bool =
  fun b1 b2 →
    case b1 of
    | F[x] → b2
    | T[x] → tru

val or_total : ∀ x:ι, x∈bool ⇒  ∀ y:ι, y∈bool ⇒ ∃ v:ι, or x y ≡ v =
  fun b1 b2 →
    case b1 of
    | F[x] → {}
    | T[x] → {}

val and : bool ⇒ bool ⇒ bool =
  fun b1 → fun b2 →
    case b1 of
    | F[x] → fls
    | T[x] → b2

val and_total : ∀ x:ι, x∈bool ⇒  ∀ y:ι, y∈bool ⇒ ∃ v:ι, and x y ≡ v =
  fun b1 b2 →
    case b1 of
    | F[x] → {}
    | T[x] → {}

// Proof of the excluded middle
val excluded_middle : ∀ x:ι, x∈bool ⇒ or x (not x) ≡ tru =
  fun b →
    case b of
    | F[x] → {}
    | T[x] → {}

// Equivalence is reflexive.
val eq_refl : ∀ x:ι, x∈bool ⇒ eq x x ≡ tru =
  fun b →
    case b of
    | F[x] → {}
    | T[x] → {}

// Equivalence is commutative.
val eq_comm : ∀ x:ι, ∀ y:ι, x∈bool ⇒ y∈bool ⇒ eq x y ≡ eq y x =
  fun b1 b2 →
    case b1 of
    | F[x] → (case b2 of | T[y] → {} | F[y] → {})
    | T[x] → (case b2 of | T[y] → {} | F[y] → {})

val eq_comm2 : ∀ x:ι, ∀ y:ι, x∈bool ⇒ y∈bool ⇒ eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    case b1 of
    | F[x] → (case b2 of | T[y] → {} | F[y] → {})
    | T[x] → (case b2 of | T[y] → {} | F[y] → {})

// Equivalence is associative.
val eq_asso : ∀ x:ι, ∀ y:ι, ∀ z:ι, x∈bool ⇒ y∈bool ⇒ z∈bool ⇒
              eq (eq x y) z ≡ eq x (eq y z) =
  fun b1 b2 b3 →
    case b1 of
    | F[x] → (case b2 of
              | T[y] → (case b3 of | T[z] → {} | F[z] → {})
              | F[y] → (case b3 of | T[z] → {} | F[z] → {}))
    | T[x] → (case b2 of
              | T[y] → (case b3 of | T[z] → {} | F[z] → {})
              | F[y] → (case b3 of | T[z] → {} | F[z] → {}))

// Other version using "let".
val eq_comm3 : ∀ x:ι, ∀ y:ι, x∈bool ⇒ y∈bool ⇒ eq (eq x y) (eq y x) ≡ tru =
  fun b1 b2 →
    let lem1 = eq_comm b1 b2 in
    let lem0 = eq_total b1 b2 in
    let lem2 = eq_refl (eq b1 b2) in
    {}
