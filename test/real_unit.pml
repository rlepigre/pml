// Usual « unit » type (i.e. empty product).
def unit : ο = {}

// It is inhabited by the empty record.
val u : unit = {}

// It is in fact inhabited by any record...
val u_aux : unit = {l = {}}


// We can define a real (one element) « unit » type as follows.
def real_unit : ο = ∃ x:ι, (x ∈ {}) | x ≡ {}

// It is still inhabited by the empty record.
val unit : real_unit = {}


// But any other record is not in this type.
// val unit_bad : real_unit = {l = {}}

// In fact we can prove that every value of [real_unit] is equivalent
// to the empty record [{}].
val canonical : ∀ x:ι, x∈real_unit ⇒ x ≡ {} = fun x → x

// More things
def real_bool : ο = [T of real_unit ; F of real_unit]

val is_realbool : ∀ x:ι, x∈real_bool ⇒ [L of x ≡ T[{}] ; R of x ≡ F[{}]] =
  fun x →
    case x of
    | F[e] → R[e]
    | T[e] → L[e]

val tru : real_bool = T[{}]
val fls : real_bool = F[{}]

// Basic functions.
val eq : real_bool ⇒ real_bool ⇒ real_bool =
  fun b1 b2 →
    case b1 of
    | F[x] → (case b2 of
              | T[y] → fls
              | F[y] → tru)
    | T[x] → (case b2 of
              | T[y] → tru
              | F[y] → fls)

// Equivalence is total.
val eq_total :  ∀ x:ι, x∈real_bool ⇒  ∀ y:ι, y∈real_bool ⇒ ∃ v:ι, eq x y ≡ v =
  fun b1 b2 →
    case b1 of
    | F[x] → (case b2 of | T[y] → {} | F[y] → {})
    | T[x] → (case b2 of | T[y] → {} | F[y] → {})

val arg_bool :  ∀ x:ι, x∈real_bool ⇒ {} =
  fun b → case b of | T[v] → v | F[v] → v

val is_realbool2 : ∀ x:ι, x∈real_bool ⇒ arg_bool x ≡ {} =
  fun b →
    case is_realbool b of
    | L[e] → {}
    | R[e] → {}

val is_realbool3 : ∀ x:ι, x∈real_bool ⇒ arg_bool x ≡ {} =
  fun x →
    case x of
    | T[e] → {}
    | F[e] → {}


//val eq_eq : ∀ x:ι, ∀ y:ι, x∈real_bool ⇒ y∈real_bool ⇒ eq x y ≡ tru ⇒ x ≡ y =
//  fun b1 b2 e →
//    case is_realbool b1 of
//    | L[u] → (case is_realbool b2 of | L[u] → {} | R[u] → {})
//    | R[u] → (case is_realbool b2 of | L[u] → {} | R[u] → {})
