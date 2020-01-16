
val rec loop : ∀a b, a ⇏ b = fun x { loop x }

//val test : ∀a, a = loop {}