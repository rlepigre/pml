// Short names for the booleans.
val tru : bool = true
val fls : bool = false

// Lazy conditionals.
def cond<c:τ,t:τ,e:τ> = if c { t } else { e }

def land<a:τ,b:τ> = cond<a,b,fls>
def lor <a:τ,b:τ> = cond<a,tru,b>

val not : bool ⇒ bool = fun a { cond<a, fls, tru> }

val and : bool ⇒ bool ⇒ bool = fun a b { cond<a, b, fls> }

val or  : bool ⇒ bool ⇒ bool = fun a b { cond<a, tru, b> }

val xor : bool ⇒ bool ⇒ bool = fun a b { cond<a, not b, b> }

val imp : bool ⇒ bool ⇒ bool = fun a b { cond<a, b, tru> }

val eq  : bool ⇒ bool ⇒ bool = fun a b { cond<a, b, not b> }
