def unit : ο = {}
def null : ο = []
def arrow (a : ο) (b : ο) : ο = a ⇒ b
def delta : ι = λx.x x
def omega : τ = delta delta
def fixid : τ = fix (λx.x)
