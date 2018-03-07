
def land⟨a:τ,b:τ⟩ = if a { b } else { false }
def lor ⟨a:τ,b:τ⟩ = if a { true } else { b }
def limp⟨a:τ,b:τ⟩ = if a { b } else { true }

infix (&&) = land⟨⟩ priority 6 right associative
infix (||) = lor ⟨⟩ priority 7 right associative
infix (=>) = limp⟨⟩ priority 8 right associative

val not : bool ⇒ bool = fun a { if a { false } else { true } }

val and : bool ⇒ bool ⇒ bool = fun a b { a && b }

val or  : bool ⇒ bool ⇒ bool = fun a b { a || b }

val xor : bool ⇒ bool ⇒ bool = fun a b { if a { not b } else { b } }

val imp : bool ⇒ bool ⇒ bool = fun a b { a => b }

val eq  : bool ⇒ bool ⇒ bool = fun a b { if a { b } else { not b } }

val print_bool : bool ⇒ {} =
  fun b { if b { print "true " } else { print "false" } }

val println_bool : bool ⇒ {} =
  fun b { print_bool b; print "\n" }
