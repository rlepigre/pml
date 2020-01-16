include lib.either
include lib.list
include lib.bool
include lib.nat

// use hoas + parametricity to give a type containing
// only closed lambda-terms.
type rec pterm⟨v⟩ =
  [ Var of v
  ; Lam of v ⇒ pterm⟨v⟩
  ; App of pterm⟨v⟩ × pterm⟨v⟩
  ]

type term = ∀v, pterm⟨v⟩

// A few terms
val idt : term = Lam[fun x { Var[x] }]

val delta : term = Lam[fun x { App[(Var[x],Var[x])] }]

val omega : term = App[(delta,delta)]

val church : nat ⇒ term = fun n {
  Lam[fun f {
      Lam[fun x {
          let v such that _ : pterm⟨v⟩;
          let rec fn : nat ⇒ pterm⟨v⟩ = fun n {
            case n {
              Zero → Var[x]
              S[p] → App[(Var[f], fn p)]
            }
          }; fn n
        }]
    }]
}

// printing for terms
val rec print_term_aux : nat ⇒ pterm⟨nat⟩ ⇒ {} = fun i t {
  case t {
    Var[i]       → print_nat i
    App[(t1,t2)] → print "("; print_term_aux i t1;
                   print " "; print_term_aux i t2;
                   print ")"
    Lam[f]       → print "%"; print_nat i;
                   print "."; print_term_aux S[i] (f i)
  }
}

val print_term : term ⇒ {} = fun t { print_term_aux 0 t; print "\n"; {} }

val test0 : {} = print_term omega
val testn : {} = print_term (church 10)

// equality on terms ( ≡ does not work because function equality in pml
// is too weak. Is this a bug ?
val rec eq_aux : nat ⇒ pterm⟨nat⟩ ⇒ pterm⟨nat⟩ ⇒ bool = fun i t1 t2 {
  case t1 {
    App[(u1,v1)] →
      case t2 {
        App[(u2,v2)] → land⟨eq_aux i u1 u2, eq_aux i v1 v2⟩
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

val eq : term ⇒ term ⇒ bool = eq_aux 0

// The very important lifting function
val rec lift : ∀v, pterm⟨either⟨v, pterm⟨v⟩⟩⟩ ⇒ pterm⟨v⟩ = fun t {
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
val subst_aux : term ⇒ ∀v, pterm⟨v⟩ ⇒ pterm⟨v⟩ = fun t1 t2 {
  let v such that _:pterm⟨v⟩;
  let t1' : pterm⟨either⟨v, pterm⟨v⟩⟩⟩ = t1;
  let t2  : either⟨v, pterm⟨v⟩⟩ = InR[t2];
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
type path = list⟨path_elt⟩

val rec red_one : ∀v, path ⇒ pterm⟨either⟨v, pterm⟨v⟩⟩⟩ ⇒ pterm⟨v⟩ = fun p t {
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
val rec red : list⟨path⟩ ⇒ term ⇒ term = fun ps t {
  case ps {
    []    → t
    p::ps → red ps (red_one p t)
  }
}

// type for beta !
type beta⟨t1,t2⟩ = { ps∈list⟨path⟩ | eq (red ps t1) t2 }

// Tests
val test1 : {} = print_term (red_one [] omega)

val test2 : omega ≡ omega = {}

//val test3 : omega ≡ (red_one [] omega) = {} // fails !!!

val test4 : eq omega (red_one [] omega) ≡ true = {}

val test5 : beta⟨omega,omega⟩ = []::[]

val test6 : beta⟨omega,omega⟩ = []::[]::[]

val test7 : beta⟨App[(idt,omega)],omega⟩ = []::[]::[]

// reduction parrallel

type rec ptree =
  [ Idt
  ; Rdx of ptree × ptree
  ; App of ptree × ptree
  ; Lam of ptree
  ]

val rec par_red_one : ∀v, ptree ⇒ pterm⟨either⟨v, pterm⟨v⟩⟩⟩ ⇒ pterm⟨v⟩ = fun p t {
  case p {
    Idt          → lift t
    Rdx[(p1,p2)] →
      case t {
        App[(t1,t2)] →
          case t1 {
            Lam[f] → par_red_one p1 (f (InR[par_red_one p2 t2]))
            App[_] → lift t
            Var[_] → lift t
          }
        Lam[_]       → lift t
        Var[_]       → lift t
      }
    App[(p1,p2)]   →
      case t {
        App[(t1,t2)] → App[(par_red_one p1 t1, par_red_one p2 t2)]
        Lam[_]       → lift t
        Var[_]       → lift t
      }
    Lam[p1]      →
      case t {
        Lam[f] → Lam[fun v { par_red_one p1 (f InL[v])}]
        App[_] → lift t
        Var[_] → lift t
      }
  }
}

val par_red_one : ptree ⇒ term ⇒ term = par_red_one

// multiple step parallel reduction
val rec par_red : list⟨ptree⟩ ⇒ term ⇒ term = fun ps t {
  case ps {
    []    → t
    p::ps → par_red ps (par_red_one p t)
  }
}

// type for parallel beta !
type beta_par⟨t1,t2⟩ = { ps∈list⟨ptree⟩ | eq (par_red ps t1) t2 }

// test parallel reduction
val test8 : beta_par⟨App[(App[(idt,delta)],App[(idt,delta)])],omega⟩ =
  App[(Rdx[(Idt,Idt)],Rdx[(Idt,Idt)])]::Rdx[(Idt,Idt)]::[]

val is_idt : ptree ⇒ bool = fun t1 {
  case t1 {
    Idt → true
    App[_] → false
    Rdx[_] → false
    Lam[_] → false
  }
}

val app : ptree ⇒ ptree ⇒ ptree = fun t1 t2 {
  if land⟨is_idt t1, is_idt t2⟩ { Idt } else { App[(t1,t2)] }
}

val lam : ptree ⇒ ptree = fun t1 {
  if is_idt t1 { Idt } else { Lam[t1] }
}

// search all redexes, ensure that we return Idt if no redex
val rec redexes : pterm⟨{}⟩ ⇒ ptree = fun t {
  case t {
    Var[_]       → Idt
    Lam[f]       → lam (redexes(f {}))
    App[(t1,t2)] → case t1 {
      Lam[f] → Rdx[(redexes(f {}), redexes t2)]
      Var[_] → app (redexes t1) (redexes t2)
      App[_] → app (redexes t1) (redexes t2)
    }
  }
}


val redexes : term ⇒ ptree = redexes

// using redexes, we can define complete development
val complete_dev : term ⇒ term = fun t {
  par_red_one (redexes t) t
}

// and (non terminating) normalisation
val rec normalise : term ↛ term = fun t {
  let p = redexes t;
  if is_idt p { t } else { normalise (par_red_one p t) }
}

val test9 : eq (normalise (App[(church 2, church 2)])) (church 4) = {}

val test10 : eq (normalise (App[(church 2, church 3)])) (church 9) = {}

val test11 : eq (normalise (App[(church 3, church 2)])) (church 8) = {}
