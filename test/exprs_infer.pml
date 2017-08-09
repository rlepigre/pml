def unit = {}
def null = []
def triv = {} ⇒ []
def blop = ∀ x, x
def id = λx.x
def stack = (λx.x) · ε
def delta = λx.x x
def omega = delta delta
def arrow<a, b> = a ⇒ b

def test1 =
  case C[{}] {
    | C[z] → z
    | D[w] → C[w]
  }

def test2 =
  case (λx.x) C[{}] {
    | C[z] → z
    | D[w] → C[w]
  }

def fixid = fix (λx.x)

def lamb_v = λx.x

def lamb_t = λx.x

def muI = μa.[a]λx.x
def mua = μa b.λx.x
def mub = μa b.[a]λx.x
def muc = μa b.λx.[b]x
def mud = μa b.[a]λx.[b]x

def app3<a, b, c> = a b c
