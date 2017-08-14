type wrong_unit = {⋯}

// It is inhabited by the empty record.
val u : wrong_unit = {}

// And in fact by any record...
val u_aux : wrong_unit = {l = {}}
type unit1 = {} ∈ {⋯}
type unit2 = ∃x:ι, x ∈ ({⋯} | x ≡ {})
type unit3 = ∃x:ι, x ∈ {⋯} | x ≡ {}
def unit : ο = {} ∈ {⋯}
// def unit : ο = {}

// It is inhabited by the empty record.
val u : unit = {}

// But not by any other record.
// val fail : unit = {l = {}}
val true_unit : ∀x∈unit, x ≡ {} = fun x { {} }
