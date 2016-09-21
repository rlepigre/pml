def unit : ο = {}
def null : ο = []
def triv : ο = {} ⇒ []
def blop = ∀ (x : ο) x
def id = λx.x
def stack = (λx.x) . ε
def delta = λx.x x

def omega : τ = delta delta

def arrow (a : ο) (b : ο) : ο = a ⇒ b
// def fixid : τ = fix (λx.x)
// 
// def test_case : τ =
//   case (λx.x) C[{}] of
//   | C[z] → z
//   | D[w] → C[w]
