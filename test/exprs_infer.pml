def unit = {}
def null = ∅
def triv = {} ⇒ ∅
def blop = ∀ x, x
def id = fun x { x }
def stack = (fun x { x }) · ε
def delta = fun x { x x }
def omega = delta delta
def arrow<a, b> = a ⇒ b

def test1 =
  case C[{}] {
    | C[z] → z
    | D[w] → C[w]
  }

def test2 =
  case (fun x { x }) C[{}] {
    | C[z] → z
    | D[w] → C[w]
  }

def lamb_v = fun x { x }

def lamb_t = fun x { x }

def muI = save a { restore a (fun x { x }) }
def mua = save a { fun x { x } }
def mub = save a { restore a (fun x { x }) }
def mud = save a { save b { restore a (fun x { restore b x }) } }

def app3<a, b, c> = a b c
