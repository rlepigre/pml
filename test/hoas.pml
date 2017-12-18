include lib.either
include lib.list
include lib.bool
include lib.nat

// use hoas + parametricity to give a type containing
// only closed lambda-terms.
type rec pterm<v> =
  [ Var of v
  ; Lam of v ⇒ pterm
  ; App of pterm × pterm
  ]

type term = ∀v, pterm<v>

// A few terms
val idt : term = Lam[fun x { Var[x] }]

val delta : term = Lam[fun x { App[(Var[x],Var[x])] }]

val omega : term = App[(delta,delta)]

val church : nat ⇒ term = fun n {
  Lam[fun f {
      Lam[fun x {
          let v such that _ : pterm<v>;
          let rec fn : nat ⇒ pterm<v> = fun n {
            case n {
              Zero → Var[x]
              S[p] → App[(Var[f], fn p)]
            }
          }; fn n
        }]
    }]
}

// printing for terms
val rec print_term_aux : nat ⇒ pterm<nat> ⇒ {} = fun i t {
  case t {
    Var[i]       → print_nat i
    App[(t1,t2)] → print "("; print_term_aux i t1;
                   print " "; print_term_aux i t2;
                   print ")"
    Lam[f]       → print "%"; print_nat i;
                   print "."; print_term_aux S[i] (f i)
  }
}

val print_term : term → {} = fun t { print_term_aux u0 t; print "\n"; {} }

val test0 : {} = print_term omega
val testn : {} = print_term (church u10)

// equality on terms ( ≡ does not work because function equality in pml
// is too weak. Is this a bug ?
val rec eq_aux : nat ⇒ pterm<nat> ⇒ pterm<nat> ⇒ bool = fun i t1 t2 {
  case t1 {
    App[(u1,v1)] →
      case t2 {
        App[(u2,v2)] → land<eq_aux i u1 u2, eq_aux i v1 v2>
        Lam[_]       → false
        Var[_]       → false
      }
    Lam[f1]      →
      case t2 {
        App[(u2,v2)] → false
        Lam[f2]      → eq_aux S[i] (f1 i) (f2 i)
        Var[_]       → false
      }
    Var[i1]      →
      case t2 {
        App[(u2,v2)] → false
        Lam[f2]      → false
        Var[i2]      → eq i1 i2
      }
  }
}

val eq : term ⇒ term ⇒ bool = eq_aux u0

// The very important lifting function
val rec lift : ∀v, pterm<either<v, pterm<v>>> ⇒ pterm<v> = fun t {
  case t {
    Var[v]       →  case v {
      InL[v] → Var[v]
      InR[t] → t
    }
    Lam[f]       →
      Lam[fun v { lift (f InL[v]) }]
    App[(t1,t2)] →
      App[(lift t1, lift t2)]
  }
}

// substitution (usefull ?)
val subst_aux : term ⇒ ∀v, pterm<v> ⇒ pterm<v> = fun t1 t2 {
  let v such that _:pterm<v>;
  let t1' : pterm<either<v, pterm<v>>> = t1;
  let t2  : either<v, pterm<v>> = InR[t2];
  case t1' {
    Var[_] → t1
    App[_] → t1
    Lam[f] → lift (f t2)
  }
}

val subst : term ⇒ term ⇒ term = subst_aux

// one step reduction, at a position.
// if the position is wrong, returns the initial term
type path_elt = [Lam ; AppL ; AppR]
type path = list<path_elt>

val rec red_one : ∀v, path ⇒ pterm<either<v, pterm<v>>> ⇒ pterm<v> = fun p t {
  case p {
    [] →
      case t {
        App[(t1,t2)] →
          case t1 {
            Lam[f] → lift (f (InR[lift t2]))
            App[_] → lift t
            Var[_] → lift t
          }
        Lam[_] → lift t
        Var[_] → lift t
      }
    x::p → case x {
      AppL →
        case t {
          App[(t1,t2)] → App[(red_one p t1, lift t2)]
          Lam[_]       → lift t
          Var[_]       → lift t
        }
      AppR →
        case t {
          App[(t1,t2)] → App[(lift t1, red_one p t2)]
          Lam[_]       → lift t
          Var[_]       → lift t
        }
      Lam →
        case t {
          Lam[f] → Lam[fun v { red_one p (f InL[v])}]
          App[_] → lift t
          Var[_] → lift t
        }
    }
  }
}

val red_one :  path ⇒ term ⇒ term = red_one

// multiple step reduction
val rec red : list<path> ⇒ term ⇒ term = fun ps t {
  case ps {
    []    → t
    p::ps → red ps (red_one p t)
  }
}

// type for beta !
type beta<t1,t2> = { ps∈list<path> | eq (red ps t1) t2 }

// Tests
val test1 : {} = print_term (red_one [] omega)

val test2 : omega ≡ omega = {}

//val test3 : omega ≡ (red_one [] omega) = {} // fails !!!

val test4 : eq omega (red_one [] omega) ≡ true = {}

val test5 : beta<omega,omega> = []::[]

val test6 : beta<omega,omega> = []::[]::[]

val test7 : beta<App[(idt,omega)],omega> = []::[]::[]
