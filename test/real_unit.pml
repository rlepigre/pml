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
