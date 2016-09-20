def unit : ο = {}
def null : ο = []
def arrow (a : ο) (b : ο) : ο = a ⇒ b
def delta : ι = λx.x x
def omega : τ = delta delta
def fixid : τ = fix (λx.x)
def stack : σ = (λx.x) . ε

def test_case : τ =
  case (λx.x) C[{}] of
  | C[z] → z
  | D[w] → C[w]
