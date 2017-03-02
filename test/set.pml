include lib.prelude

type set = ∃a:ο, a ⇒ bool

val all : set = fun x → tru

val all_in_all : all all ≡ tru = {}
