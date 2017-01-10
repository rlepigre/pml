// Booleans

// Type of booleans
def bool : ο = [F of {} ; T of {}]

// Smart constructors
val tru : bool = T[]
val fls : bool = F[]

// Basic functions.
val not : bool ⇒ bool =
  fun b →
    case b of
    | F[x] → tru
    | T[x] → fls

val or : bool ⇒ bool ⇒ bool =
  fun b1 b2 →
    case b1 of
    | F[x] → b2
    | T[x] → tru

val and : bool ⇒ bool ⇒ bool =
  fun b1 b2 →
    case b1 of
    | F[x] → fls
    | T[x] → b2

// Proof of the excluded middle
//val excluded_middle : ∀ (x : ι) x∈bool ⇒ ((or x) (not x)) ≡ tru =
//  fun b →
//    case b of
//    | F[x] → {}
//    | T[x] → {}
