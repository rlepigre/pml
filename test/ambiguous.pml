def fst<a:τ, y:τ> : τ = a

val test : {} = fst<{l = λx.x}.l {}, {}>
