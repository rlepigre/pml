type set = ∃a:ο, a ⇒ bool

val all : set = fun x { true }

val all_in_all : all all ≡ true = {}
