type unit1 = {}
type unit2 = {} ∈ {⋯}
type unit3 = ∃x:ι, x∈({⋯} | x ≡ {})
type unit4 = ∃x:ι, x∈{⋯} | x ≡ {}

assert unit1 ⊂ unit2
assert unit2 ⊂ unit1
assert unit1 ⊂ unit3
assert unit3 ⊂ unit1
assert unit1 ⊂ unit4
assert unit4 ⊂ unit1
assert unit2 ⊂ unit3
assert unit3 ⊂ unit2
assert unit2 ⊂ unit4
assert unit4 ⊂ unit2
assert unit3 ⊂ unit4
assert unit4 ⊂ unit3
