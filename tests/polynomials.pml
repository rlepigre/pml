include lib.nat
include lib.nat_proofs
include lib.list
include lib.comparison
include lib.bool

// signature of commutative semi ring (like nat)
type semiring⟨x⟩ = ∃zero one (+) (*):ι, {
  zero : zero∈x;
  one  : one∈x;
  (+)  : (+)∈(x ⇒ x ⇒ x);
  (*)  : (*)∈(x ⇒ x ⇒ x);
  add_neutral : ∀a∈x,        zero + a ≡ a;
  add_assoc   : ∀a b c∈x, a + (b + c) ≡ (a + b) + c;
  add_comm    : ∀a b∈x,         a + b ≡ b + a;
  mul_neutral : ∀a∈x,         one * a ≡ a;
  mul_abs     : ∀a∈x,        zero * a ≡ zero;
  mul_assoc   : ∀a b c∈x, a * (b * c) ≡ (a * b) * c;
  mul_comm    : ∀a b∈x,         a * b ≡ b * a;
  mul_distrib : ∀a b c∈x, a * (b + c) ≡ (a * b) + (a * c);
  ⋯
  }

// any semi ring has an exponential
val rec exp_ring : ∀r, semiring⟨r⟩ ⇒ r ⇒ nat ⇒ r = fun s x n {
  case n {
    Zero → s.one
    S[p] → let exp = exp_ring s; x *_s (x ** p)
  }
}

val rec exp_add : ∀r, ∀s∈semiring⟨r⟩, ∀x∈r, ∀a b∈nat,
                    exp_ring s x (a + b) ≡ (exp_ring s x a) *_s (exp_ring s x b) =
  fun s x a b {
    let exp = exp_ring s;
    case a {
      Zero → deduce x ** (a + b) ≡ x ** b;
             deduce x ** a *_s x ** b ≡ s.one *_s (x ** b);
             use s.mul_neutral (x ** b);
             deduce (x ** a) *_s (x ** b) ≡ x ** b;
             qed
      S[p] → deduce x ** (a + b) ≡ x *_s x ** (p + b);
             deduce x ** a *_s x ** b ≡ x *_s x ** p *_s x ** b;
             show x ** (a + b) ≡ x *_s (x ** p *_s x ** b) using exp_add s x p b;
             show x ** (a + b) ≡ x *_s x ** p *_s x ** b using s.mul_assoc x (x ** p) (x ** b);
             qed
    }
  }
///////////////////////////////
// definition of polynomials //
///////////////////////////////

// monom: list of natural numbers: a::b::c::[] ⇒ x0^a + x1^a + x2^a
// one shoud avoid trailing Zero.
type monom = list⟨nat⟩

// lexicographic ordering on monomials
val rec lex : ∀m1 m2∈monom, dcmp⟨m1,m2⟩ = fun m1 m2 {
  case m1 {
    []     → case m2 {
      []     → Eq
      n2::p2 → Ls
    }
    n1::p1 → case m2 {
      []     → Gr
      n2::p2 → case compare n1 n2 {
        Ls → Ls
        Gr → Gr
        Eq → lex p1 p2 }
    }
  }
}

// Stricly less monomial
val less : monom ⇒ monom ⇒ bool = fun m1 m2 {
  case lex m1 m2 {
    Ls → true
    Eq → false
    Gr → false
  }
}

// polynomial
type poly⟨x⟩ = list⟨x × monom⟩

// Polynomials should be sorted with no duplicate.
// not really usefull for reflexion.
val rec sorted : ∀x, poly⟨x⟩ ⇒ bool = fun p {
  case p {
    []   → true
    c::q → let (x,m) = c;
           case q {
             []   → true
             c::r → let (y,n) = c;
                    land⟨less m n, sorted q⟩
           }
  }
}

// normalised polynomial
type npoly⟨x⟩ = {l∈poly⟨x⟩ | sorted l}

///////////////////////////////
// operations on polynomials //
///////////////////////////////

// addition, the fact that we keep the invariant is unproved yed
val rec add_poly
        : ∀x, semiring⟨x⟩ ⇒ poly⟨x⟩ ⇒ poly⟨x⟩ ⇒ poly⟨x⟩ =
  fun r p1 p2 {
    case p1 {
      []    → p2
      c::q1 → let (x1,m1) = c;
              case p2 {
                []    → p1
                c::q2 → let (x2,m2) = c;
                        case lex m1 m2 {
                          Ls → (x1,m1) :: add_poly r q1 p2
                          Eq → (x1 +_r x2, m1) :: add_poly r q1 q2
                          Gr → (x2,m2) :: add_poly r p1 q2
                        }
              }
    }
  }

// monomial multiplication is addition
val rec mul_monom : monom ⇒ monom ⇒ monom = fun m1 m2 {
  case m1 {
    []     → m2
    e1::p1 → case m2 {
      []     → m1
      e2::p2 → add e1 e2 :: mul_monom p1 p2
    }
  }
}

// multiplication of a polynomial as a coef and a monomial
val rec mul_monom_poly : ∀r, semiring⟨r⟩ ⇒ r ⇒ monom ⇒ list⟨r×monom⟩ ⇒ list⟨r×monom⟩ =
  fun s x m1 p {
    case p {
      []   → []
      c::q → let (y,m2) = c;
             (s.mul x y, mul_monom m1 m2) :: mul_monom_poly s x m1 q
    }
  }

// polynomial multiplication
val rec mul_poly : ∀r, semiring⟨r⟩ ⇒ list⟨r×monom⟩ ⇒ list⟨r×monom⟩ ⇒ list⟨r×monom⟩ =
  fun s p1 p2 {
    let r such that _:list⟨r×monom⟩;
    let fn : r×monom ⇒ list⟨r×monom⟩ ⇒ list⟨r×monom⟩ = fun c p {
      let (x,m) = c;
      add_poly s p (mul_monom_poly s x m p2)
    };
    fold_right fn p1 []
  }

// polynomial exponentiation
val rec exp_poly : ∀r, semiring⟨r⟩ ⇒ list⟨r×monom⟩ ⇒ nat ⇒ list⟨r×monom⟩ =
  fun s p n {
    case n {
      Zero → (s.one,[]) :: []
      S[m] → mul_poly s p (exp_poly s p m)
    }
  }

///////////////////////////////
// evaluation of polynomials //
///////////////////////////////

val rec eval_monom : ∀r, semiring⟨r⟩ ⇒ monom ⇒ (nat ⇒ r) ⇒ nat ⇒ r = fun s m env i {
  case m {
    [] → s.one
    x::m →
      let exp = exp_ring s;
      s.mul (eval_monom s m env (succ i)) (exp (env i) x)
  }
}

val rec eval : ∀x, semiring⟨x⟩ ⇒ poly⟨x⟩ ⇒ (nat ⇒ x) ⇒ x = fun r p env {
  case p {
    []   → r.zero
    c::p → let (x,m) = c;
           r.add (r.mul x (eval_monom r m env Zero)) (eval r p env)
  }
}

///////////////////////////////
//    polynomials as trees   //
///////////////////////////////

type rec tpoly⟨x⟩ =
  [ Var of nat
  ; Cst of x
  ; Add of tpoly⟨x⟩ × tpoly⟨x⟩
  ; Mul of tpoly⟨x⟩ × tpoly⟨x⟩
  ; Exp of tpoly⟨x⟩ × nat
  ]

val add_p : ∀a, tpoly⟨a⟩ ⇒ tpoly⟨a⟩ ⇒ tpoly⟨a⟩ = fun x y { Add[(x,y)] }
infix (+~) = add_p priority 3 left associative
val mul_p : ∀a, tpoly⟨a⟩ ⇒ tpoly⟨a⟩ ⇒ tpoly⟨a⟩ = fun x y { Mul[(x,y)] }
infix (*~) = mul_p priority 2 left associative
val exp_p : ∀a, tpoly⟨a⟩ ⇒ nat ⇒ tpoly⟨a⟩ = fun x y { Exp[(x,y)] }
infix (**~) = exp_p priority 1 right associative

val rec var : nat ⇒ monom = fun n {
  case n {
    Zero → 1::[]
    S[p] → 0::var p
  }
}

// conversion (develop)
val rec tpoly_to_poly : ∀r, semiring⟨r⟩ ⇒ tpoly⟨r⟩ ⇒ list⟨r×monom⟩ = fun s t {
  case t {
    Var[n]       → (s.one, var n) :: []
    Cst[x]       → (x    , []   ) :: []
    Add[(p1,p2)] → add_poly s (tpoly_to_poly s p1) (tpoly_to_poly s p2)
    Mul[(p1,p2)] → mul_poly s (tpoly_to_poly s p1) (tpoly_to_poly s p2)
    Exp[(p1,n)]  → exp_poly s (tpoly_to_poly s p1) n
  }
}

// evaluation of trees
val rec teval : ∀r, semiring⟨r⟩ ⇒ tpoly⟨r⟩ ⇒ (nat ⇒ r) ⇒ r = fun s t env {
  case t {
    Var[n]       → env n
    Cst[x]       → x
    Add[(p1,p2)] → s.add (teval s p1 env) (teval s p2 env)
    Mul[(p1,p2)] → s.mul (teval s p1 env) (teval s p2 env)
    Exp[(p1,n)]  → exp_ring s (teval s p1 env) n
  }
}

///////////////////////////////
//    main theorems: lemmas  //
///////////////////////////////

val rec eval_monom_var : ∀r, ∀s∈semiring⟨r⟩, ∀n∈nat, ∀env∈(nat ⇒ r), ∀i∈nat,
                       eval_monom s (var n) env i ≡ env (add i n) =
  fun s n env i {
    case n {
      Zero → deduce eval_monom s (var n) env i ≡ s.mul s.one (exp_ring s (env i) 1);
             deduce exp_ring s (env i) 1 ≡ s.mul (env i) s.one;
             use s.mul_comm (env i) s.one;
             use s.mul_neutral (env i);
             deduce eval_monom s (var n) env i ≡ env i;
             use add_n_zero i;
             qed
      S[p] → set auto 0 2;
             deduce var n ≡ Zero :: var p;
             deduce eval_monom s (var n) env i ≡
               s.mul (eval_monom s (var p) env S[i]) s.one;
             show eval_monom s (var p) env S[i] ≡ env (add S[i] p)
               using eval_monom_var s p env S[i];
             show add S[i] p ≡ add i n using add_n_succ i p;
             deduce eval_monom s (var n) env i ≡
               s.mul (env (add i n)) s.one;
             use s.mul_comm (env (add i n)) s.one;
             use s.mul_neutral (env (add i n));
             qed
    }
  }

val eval_var : ∀r, ∀s∈semiring⟨r⟩,  ∀n∈nat, ∀env∈(nat ⇒ r),
                 eval s (tpoly_to_poly s Var[n]) env ≡ env n =
  fun s n env {
    let t = Var[n];
    deduce teval s t env ≡ env n;
    deduce tpoly_to_poly s t ≡ (s.one, var n) :: [];
    show eval_monom s (var n) env Zero ≡ env n
      using eval_monom_var s n env Zero;
    deduce eval s (tpoly_to_poly s Var[n]) env ≡ s.add (s.mul s.one (env n)) s.zero;
    use s.mul_neutral (env n);
    use s.add_comm (env n) s.zero;
    use s.add_neutral (env n);
    deduce eval s (tpoly_to_poly s Var[n]) env ≡ env n;
    qed
   }

val eval_cst : ∀r, ∀s∈semiring⟨r⟩,  ∀x∈r, ∀env∈(nat ⇒ r),
                 eval s (tpoly_to_poly s Cst[x]) env ≡ x =
  fun s x env {
    let t = Cst[x];
    deduce tpoly_to_poly s t ≡ (x, []) :: [];
    deduce eval s (tpoly_to_poly s t) env ≡ s.add (s.mul x s.one) s.zero;
    use s.mul_comm x s.one;
    use s.mul_neutral x;
    use s.add_comm x s.zero;
    use s.add_neutral x;
    qed
  }

val rec eval_add : ∀r, ∀s∈semiring⟨r⟩,  ∀p1 p2∈list⟨r×monom⟩, ∀env∈(nat ⇒ r),
                  eval s (add_poly s p1 p2) env ≡ s.add (eval s p1 env) (eval s p2 env) =
  fun s p1 p2 env {
     case p1 {
       []    →
         deduce eval s (add_poly s p1 p2) env ≡ eval s p2 env;
         deduce eval s p1 env ≡ s.zero;
         use s.add_neutral (eval s p2 env);
         qed
       c::q1 →
         let (x1,m1) = c;
         case p2 {
           []    → deduce eval s (add_poly s p1 p2) env ≡ eval s p1 env;
                   deduce eval s p2 env ≡ s.zero;
                   use s.add_comm (eval s p1 env) s.zero;
                   use s.add_neutral (eval s p1 env);
                   qed
           c::q2 →
             let (x2,m2) = c;
             case lex m1 m2 {
               Ls →
                 deduce add_poly s p1 p2 ≡ (x1,m1) :: add_poly s q1 p2;
                 let a1 = s.mul x1 (eval_monom s m1 env Zero);
                 let b1 = eval s q1 env;
                 let b2 = eval s p2 env;
                 deduce eval s (add_poly s p1 p2) env ≡
                   s.add a1 (eval s (add_poly s q1 p2) env);
                 deduce eval s p1 env ≡ s.add a1 b1;
                 show eval s (add_poly s q1 p2) env ≡ s.add b1 b2
                   using eval_add s q1 p2 env;
                 showing s.add a1 (s.add b1 b2) ≡
                   s.add (s.add a1 b1) b2;
                 use s.add_assoc a1 b1 b2;
                 qed
               Eq →
                 deduce add_poly s p1 p2 ≡
                 (s.add x1 x2, m1) :: add_poly s q1 q2;
                 deduce m1 ≡ m2;
                 let c = eval_monom s m1 env Zero;
                 let a1 = s.mul x1 c;
                 let a2 = s.mul x2 c;
                 let a  = s.mul (s.add x1 x2) c;
                 let b1 = eval s q1 env;
                 let b2 = eval s q2 env;
                 show eval s (add_poly s q1 q2) env ≡ s.add b1 b2
                   using eval_add s q1 q2 env;
                 deduce eval s (add_poly s p1 p2) env ≡
                   s.add (s.mul (s.add x1 x2) c) (s.add b1 b2);
                 deduce eval s p1 env ≡ s.add (s.mul x1 c) b1;
                 deduce eval s p2 env ≡ s.add (s.mul x2 c) b2;
                 showing s.add (s.mul (s.add x1 x2) c) (s.add b1 b2) ≡
                   s.add (s.add (s.mul x1 c) b1) (s.add (s.mul x2 c) b2);
                 use s.mul_comm x1 c;
                 use s.mul_comm x2 c;
                 use s.mul_comm (s.add x1 x2) c;
                 showing s.add (s.mul c (s.add x1 x2)) (s.add b1 b2) ≡
                   s.add (s.add (s.mul c x1) b1) (s.add (s.mul c x2) b2);
                 use s.mul_distrib c x1 x2;
                 showing s.add (s.add (s.mul c x1) (s.mul c x2)) (s.add b1 b2) ≡
                   s.add (s.add (s.mul c x1) b1) (s.add (s.mul c x2) b2);
                 use s.add_assoc (s.mul c x1) (s.mul c x2) (s.add b1 b2);
                 showing s.add (s.mul c x1) (s.add (s.mul c x2) (s.add b1 b2)) ≡
                   s.add (s.add (s.mul c x1) b1) (s.add (s.mul c x2) b2);
                 use s.add_assoc (s.mul c x2) b1 b2;
                 showing s.add (s.mul c x1) (s.add (s.add (s.mul c x2) b1) b2) ≡
                               s.add (s.add (s.mul c x1) b1) (s.add (s.mul c x2) b2);
                 use s.add_comm (s.mul c x2) b1;
                 showing s.add (s.mul c x1) (s.add (s.add b1 (s.mul c x2)) b2) ≡
                   s.add (s.add (s.mul c x1) b1) (s.add (s.mul c x2) b2);
                 use s.add_assoc b1 (s.mul c x2) b2;
                 showing s.add (s.mul c x1) (s.add b1 (s.add (s.mul c x2) b2)) ≡
                   s.add (s.add (s.mul c x1) b1) (s.add (s.mul c x2) b2);
                 use s.add_assoc (s.mul c x1) b1 (s.add (s.mul c x2) b2);
                 qed
               Gr →
                 deduce add_poly s p1 p2 ≡ (x2,m2) :: add_poly s p1 q2;
                 let a2 = s.mul x2 (eval_monom s m2 env Zero);
                 let b1 = eval s p1 env;
                 let b2 = eval s q2 env;
                 deduce eval s (add_poly s p1 p2) env ≡
                   s.add a2 (eval s (add_poly s p1 q2) env);
                 deduce eval s p2 env ≡ s.add a2 b2;
                 show eval s (add_poly s p1 q2) env ≡ s.add b1 b2
                   using eval_add s p1 q2 env;
                 showing s.add a2 (s.add b1 b2) ≡
                   s.add b1 (s.add a2 b2);
                 use s.add_assoc b1 a2 b2;
                 use s.add_assoc a2 b1 b2;
                 use s.add_comm a2 b1;
                 qed
             }
         }
     }
  }

val rec eval_mul_monom : ∀r, ∀s∈semiring⟨r⟩,  ∀m1 m2∈monom, ∀env∈(nat ⇒ r), ∀i∈nat,
                       eval_monom s (mul_monom m1 m2) env i ≡
                       s.mul (eval_monom s m1 env i) (eval_monom s m2 env i) =
  fun s m1 m2 env i {
    case m1 {
      []     → use s.mul_neutral (eval_monom s m2 env i);
               qed
      e1::p1 → case m2 {
        []     → use s.mul_comm (eval_monom s m1 env i) s.one;
                 use s.mul_neutral (eval_monom s m1 env i);
                 qed
        e2::p2 → let exp = exp_ring s;
                 deduce mul_monom m1 m2 ≡ add e1 e2 :: mul_monom p1 p2;
                 deduce eval_monom s (mul_monom m1 m2) env i ≡
                   s.mul (eval_monom s (mul_monom p1 p2) env S[i])
                     (exp (env i) (add e1 e2));
                 let a1 = eval_monom s p1 env S[i];
                 let a2 = eval_monom s p2 env S[i];
                 show eval_monom s (mul_monom p1 p2) env S[i] ≡ s.mul a1 a2
                   using eval_mul_monom s p1 p2 env S[i];
                 let b1 = exp (env i) e1;
                 let b2 = exp (env i) e2;
                 show eval_monom s (mul_monom m1 m2) env i ≡
                   s.mul (eval_monom s (mul_monom p1 p2) env S[i]) (s.mul b1 b2)
                   using exp_add s (env i) e1 e2;
                 showing s.mul (s.mul a1 a2) (s.mul b1 b2) ≡
                   s.mul (s.mul a1 b1) (s.mul a2 b2);
                 use s.mul_assoc a1 a2 (s.mul b1 b2);
                 use s.mul_assoc a1 b1 (s.mul a2 b2);
                 showing s.mul a2 (s.mul b1 b2) ≡
                   s.mul b1 (s.mul a2 b2);
                 use s.mul_assoc a2 b1 b2;
                 use s.mul_assoc b1 a2 b2;
                 showing s.mul a2 b1 ≡ s.mul b1 a2;
                 use s.mul_comm a2 b1;
                 qed
      }
    }
  }

val rec eval_mul_monom_poly : ∀r, ∀s∈semiring⟨r⟩, ∀x∈r, ∀m1∈monom,
                              ∀p∈list⟨r×monom⟩, ∀env∈(nat ⇒ r),
                       eval s (mul_monom_poly s x m1 p) env ≡
                       s.mul (s.mul x (eval_monom s m1 env 0)) (eval s p env) =
  fun s x m1 p env {
    case p {
      []   → deduce mul_monom_poly s x m1 p ≡ [];
             deduce eval s (mul_monom_poly s x m1 p) env ≡ s.zero;
             showing s.mul (s.mul x (eval_monom s m1 env 0)) s.zero ≡ s.zero;
             use s.mul_comm (s.mul x (eval_monom s m1 env 0)) s.zero;
             use s.mul_abs (s.mul x (eval_monom s m1 env 0));
             qed
      c::q → let (y,m2) = c;
             let m  = mul_monom m1 m2;
             let z  = s.mul x y;
             deduce mul_monom_poly s x m1 p ≡
               (z, m) :: mul_monom_poly s x m1 q;
             deduce eval s (mul_monom_poly s x m1 p) env ≡
               s.add (s.mul z (eval_monom s m env 0))
               (eval s (mul_monom_poly s x m1 q) env);
             let a1 = eval_monom s m1 env 0;
             let a2 = eval_monom s m2 env 0;
             let b  = eval s q env;
             show eval s (mul_monom_poly s x m1 p) env ≡
               s.add (s.mul z (s.mul a1 a2))
                     (eval s (mul_monom_poly s x m1 q) env)
               using eval_mul_monom s m1 m2 env 0;
             show eval s (mul_monom_poly s x m1 p) env ≡
               s.add (s.mul z (s.mul a1 a2)) (s.mul (s.mul x a1) b)
               using eval_mul_monom_poly s x m1 q env;
             deduce eval s p env ≡ s.add (s.mul y a2) b;
             showing s.add (s.mul (s.mul x y) (s.mul a1 a2)) (s.mul (s.mul x a1) b)
               ≡ s.mul (s.mul x a1) (s.add (s.mul y a2) b);
             use s.mul_distrib (s.mul x a1) (s.mul y a2) b;
             showing s.mul (s.mul x y) (s.mul a1 a2)
               ≡ s.mul (s.mul x a1) (s.mul y a2);
             use s.mul_assoc x y (s.mul a1 a2);
             use s.mul_assoc x a1 (s.mul y a2);
             showing  s.mul y (s.mul a1 a2)
               ≡ s.mul a1 (s.mul y a2);
             use s.mul_assoc y a1 a2;
             use s.mul_assoc a1 y a2;
             use s.mul_comm y a1;
             qed
    }
  }

val rec eval_mul : ∀r, ∀s∈semiring⟨r⟩,  ∀p1 p2∈list⟨r×monom⟩, ∀env∈(nat ⇒ r),
                  eval s (mul_poly s p1 p2) env ≡ s.mul (eval s p1 env) (eval s p2 env) =
  fun s p1 p2 env {
    case p1 {
      []    → deduce mul_poly s p1 p2 ≡ [];
              showing s.zero ≡ s.mul s.zero (eval s p2 env);
              use s.mul_abs (eval s p2 env);
              qed
      c::q1 → let (x,m1) = c;
              deduce mul_poly s p1 p2 ≡
                add_poly s (mul_poly s q1 p2) (mul_monom_poly s x m1 p2);
              let a1 = eval_monom s m1 env 0;
              let b1 = eval s q1 env;
              let b = eval s p2 env;
              show eval s (mul_poly s q1 p2) env ≡ s.mul b1 b
                using eval_mul s q1 p2 env;
              show eval s (mul_monom_poly s x m1 p2) env ≡ s.mul (s.mul x a1) b
                using eval_mul_monom_poly s x m1 p2 env;
              show eval s (add_poly s (mul_poly s q1 p2) (mul_monom_poly s x m1 p2)) env ≡
                s.add (s.mul b1 b) (s.mul (s.mul x a1) b)
                using eval_add s (mul_poly s q1 p2) (mul_monom_poly s x m1 p2) env;
              showing s.add (s.mul b1 b) (s.mul (s.mul x a1) b) ≡
                s.mul (s.add (s.mul x a1) b1) b;
              use s.mul_comm b1 b;
              use s.mul_comm (s.mul x a1) b;
              use s.mul_comm (s.add (s.mul x a1) b1) b;
              showing  s.add (s.mul b b1) (s.mul b (s.mul x a1)) ≡
                s.mul b (s.add (s.mul x a1) b1);
              use s.add_comm (s.mul x a1) b1;
              showing  s.add (s.mul b b1) (s.mul b (s.mul x a1)) ≡
                s.mul b (s.add b1 (s.mul x a1));
              use s.mul_distrib b b1 (s.mul x a1);
              qed
    }
  }

val rec eval_exp : ∀r, ∀s∈semiring⟨r⟩,  ∀p∈list⟨r×monom⟩, ∀e∈nat, ∀env∈(nat ⇒ r),
                  eval s (exp_poly s p e) env ≡ exp_ring s (eval s p env) e =
  fun s p e env {
    case e {
      Zero → deduce exp_poly s p e ≡ (s.one, []) :: [];
             deduce eval s (exp_poly s p e) env ≡ s.add (s.mul s.one s.one) s.zero;
             deduce exp_ring s (eval s p env) e ≡ s.one;
             showing s.add (s.mul s.one s.one) s.zero ≡ s.one;
             use s.mul_neutral s.one;
             use s.add_comm s.one s.zero;
             use s.add_neutral s.one;
             qed
      S[f] → deduce exp_poly s p e ≡ mul_poly s p (exp_poly s p f);
             deduce exp_ring s (eval s p env) e ≡
               s.mul (eval s p env) (exp_ring s (eval s p env) f);
             show eval s (exp_poly s p e) env ≡ s.mul
               (eval s p env) (eval s (exp_poly s p f) env)
               using eval_mul s p (exp_poly s p f) env;
             use eval_exp s p f env;
             qed
    }
  }

// Main theorem
val rec eval_cor : ∀r, ∀s∈semiring⟨r⟩, ∀t∈tpoly⟨r⟩, ∀env∈(nat ⇒ r),
                teval s t env ≡ eval s (try_eval (tpoly_to_poly s t)) env =
  fun s t env {
    case t {
      Var[n]       → eval_var s n env
      Cst[x]       → eval_cst s x env
      Add[(p1,p2)] → show eval s (tpoly_to_poly s t) env ≡
                       s.add (eval s (tpoly_to_poly s p1) env) (eval s (tpoly_to_poly s p2) env)
                       using eval_add s (tpoly_to_poly s p1) (tpoly_to_poly s p2) env;
                     use eval_cor s p1 env;
                     use eval_cor s p2 env;
                     qed
      Mul[(p1,p2)] → show eval s (tpoly_to_poly s t) env ≡
                       s.mul (eval s (tpoly_to_poly s p1) env) (eval s (tpoly_to_poly s p2) env)
                       using eval_mul s (tpoly_to_poly s p1) (tpoly_to_poly s p2) env;
                     use eval_cor s p1 env;
                     use eval_cor s p2 env;
                     qed
      Exp[(p1,n)]  → show eval s (tpoly_to_poly s t) env ≡
                       exp_ring s (eval s (tpoly_to_poly s p1) env) n
                       using eval_exp s (tpoly_to_poly s p1) n env;
                     use eval_cor s p1 env;
                     qed
    }
  }

val simpl1 : ∀r, ∀s∈semiring⟨r⟩, ∀x∈r, ∀p∈tpoly⟨r⟩ ⇒ tpoly⟨r⟩,
  teval s (p Var[0]) (fun p { x }) ≡ eval s (tpoly_to_poly s (p Var[0])) (fun p { x }) =
  fun s x p {
    eval_cor s (p Var[0]) (fun p { x })
  }

val simpl2 : ∀r, ∀s∈semiring⟨r⟩, ∀x y∈r, ∀p∈tpoly⟨r⟩ ⇒ tpoly⟨r⟩ ⇒ tpoly⟨r⟩,
          teval s (p Var[0] Var[1]) (fun p { case p { Zero → x | S[p] → y} })
          ≡ eval s (tpoly_to_poly s (p Var[0] Var[1])) (fun p { case p { Zero → x | S[p] → y}}) =
  fun s x y p {
    eval_cor s (p Var[0] Var[1]) (fun p { case p { Zero → x | S[p] → y} })
  }

// Test with polynomials with integer coefficients
val semi_nat : semiring⟨nat⟩ = {
  zero = zero; one; add; mul;
  add_neutral = fun n { {} };
  add_assoc; add_comm;
  mul_neutral; mul_assoc; mul_comm;
  mul_distrib = mul_dist_l;
  mul_abs = fun n { {} }
}

// polynomial on nat as a semi ring (missing the axioms yet)
val pn : {
  zero : tpoly⟨nat⟩;
  one  : tpoly⟨nat⟩;
  cst  : nat ⇒ tpoly⟨nat⟩;
  (+)  : tpoly⟨nat⟩ ⇒ tpoly⟨nat⟩ ⇒ tpoly⟨nat⟩;
  (*)  : tpoly⟨nat⟩ ⇒ tpoly⟨nat⟩ ⇒ tpoly⟨nat⟩;
  (**) : tpoly⟨nat⟩ ⇒ nat ⇒ tpoly⟨nat⟩
} = {
  zero = Cst[0];
  one  = Cst[1];
  cst  = fun n { Cst[n] };
  (+)  = fun a b { a +~ b };
  (*)  = fun a b { a *~ b };
  (**) = fun a b { a **~ b }
  }
