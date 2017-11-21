def unit : ο = {}
def null : ο = ∅
def triv : ο = {} ⇒ ∅
def blop = ∀ x:ο, x
def id = fun x { x }
def stack = (fun x { x }) · ε
def delta = fun x { x x }
def omega : τ = delta delta
def arrow<a:ο, b:ο> : ο = a ⇒ b

def test1 : τ =
  case C[{}] {
    | C[z] → z
    | D[w] → C[w]
  }

def test2 : τ =
  case (fun x { x }) C[{}] {
    | C[z] → z
    | D[w] → C[w]
  }

def lamb_v : ι = fun x { x }

def lamb_t : τ = fun x { x }

def muI : τ = save a { restore a (fun x { x }) }
def mua : τ = save a { fun x { x } }
def mub : τ = save a { restore a (fun x { x }) }
def mud : τ = save a { save b { fun x { restore b x } } }

def app3<a:τ, b:τ, c:τ> = a b c

def test = let rec id = fun x { id x }; id
