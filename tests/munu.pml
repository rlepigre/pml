assert [A] ⊂ [A;B]
assert ¬ [A;B] ⊂ [A]

assert (μx, [A of x ; B]) ⊂ (μx, [A of x ; B ; C])
assert ¬ (μx, [A of x ; B; C]) ⊂ (μx, [A of x ; B])

assert (μx, [A of x ; B]) ⊂ (νx, [A of x ; B])
assert (μx, [A of x ; B]) ⊂ (νx, [A of x ; B ; C])

assert ¬ (νx, [A of x ; B]) ⊂ (μx, [A of x ; B])
assert ¬ (νx, [A of x ; B]) ⊂ (μx, [A of x ; B ; C])

assert (μx, νy, [A of x ; B of y]) ⊂ (νy, μx, [A of x ; B of y])
assert ¬ (νy, μx, [A of x ; B of y]) ⊂ (μx, νy, [A of x ; B of y])
