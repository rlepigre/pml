check [A] ⊂ [A;B]
check ¬ [A;B] ⊂ [A]


check μx [A of x ; B] ⊂ μx [A of x ; B ; C]
check ¬ μx [A of x ; B; C] ⊂ μx [A of x ; B]

check μx [A of x ; B] ⊂ νx [A of x ; B]
check μx [A of x ; B] ⊂ νx [A of x ; B ; C]
check ¬ νx [A of x ; B] ⊂ μx [A of x ; B]
check ¬ νx [A of x ; B] ⊂ μx [A of x ; B ; C]

check μx νy [A of x ; B of y] ⊂ νy μx [A of x ; B of y]
check ¬ νy μx [A of x ; B of y] ⊂ μx νy [A of x ; B of y]
