val id = λx.x

val fst = λx.λy.x
val snd = λx.λy.y
val cpl = λx.λy.λp.p x y

val cpl = λx.λy.{x = x; y = y}

// val delta = λx.x x
