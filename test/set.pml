type set_ = ∃a:ο, a ⇒ bool

val all : set_ = fun x { true }

val all_in_all : all all ≡ true = {}

// fails: val bad : set_ = fun (x:set_) { x x }