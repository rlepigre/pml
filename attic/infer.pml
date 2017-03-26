val id = λx.x

val fst = λx.λy.x
val snd = λx.λy.y

// NOTE: inference does not work here.
// val church_pair = λx.λy.λp.p x y

val native_pair = λx.λy.{x = x; y = y}

// NOTE: the following term is rejected.
// val delta = λx.x x

val pierce = λx.μa.x (λy.[a]y)
