include lib.nat
include lib.nat_proofs
include lib.list
include lib.comparison
include lib.bool

// signature of semi ring (like nat)
type semiring<x> = ∃zero one add mul:ι, {
  zero : zero∈x;
  one  : one∈x;
  add  : add∈(x ⇒ x ⇒ x);
  mul  : mul∈(x ⇒ x ⇒ x);
  add_neutral : ∀a∈x, add zero a ≡ a;
  add_assoc   : ∀a b c∈x, add a (add b c) ≡ add (add a b) c;
  add_comm    : ∀a b∈x, add a b ≡ add b a;
  mul_neutral : ∀a∈x, mul one a ≡ a;
  mul_assoc   : ∀a b c∈x, mul a (mul b c) ≡ mul (mul a b) c;
  mul_comm    : ∀a b∈x, mul a b ≡ mul b a;
  mul_abs     : ∀a∈x, mul zero a ≡ zero;
  mul_distrib : ∀a b c∈x, mul a (add b c) ≡ add (mul a b) (mul a c);
  ⋯
  }

// any semi ring has an exponential
val rec exp_ring : ∀r, semiring<r> ⇒ r ⇒ nat ⇒ r = fun s x n {
  case n {
    Zero → s.one
    S[p] → let exp = exp_ring s; s.mul x (exp x p)
  }
}

///////////////////////////////
// definition of polynomials //
///////////////////////////////

// monom: list of natural numbers: a::b::c::[] ⇒ x0^a + x1^a + x2^a
// one shoud avoid trailing Zero.
type monom = list<nat>

// lexicographic ordering on monomials
val rec lex : ∀m1 m2∈monom, dcmp<m1,m2> = fun m1 m2 {
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
type poly<x> = list<x × monom>

// Polynomials should be sorted with no duplicate.
// not really usefull for reflexion.
val rec sorted : ∀x, poly<x> ⇒ bool = fun p {
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
type npoly<x> = {l∈poly<x> | sorted l}

///////////////////////////////
// operations on polynomials //
///////////////////////////////

// addition, the fact that we keep the invariant is unproved yed
val rec add_poly
        : ∀x, semiring<x> ⇒ poly<x> ⇒ poly<x> ⇒ poly<x> =
  fun r p1 p2 {
    case p1 {
      []    → p2
      c::q1 → let (x1,m1) = c;
              case p2 {
                []    → p1
                c::q2 → let (x2,m2) = c;
                        case lex m1 m2 {
                          Ls → (x1,m1) :: add_poly r q1 p2
                          Eq → (r.add x1 x2, m1) :: add_poly r q1 q2
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
val mul_monom_poly : ∀r, semiring<r> ⇒ r ⇒ monom ⇒ list<r×monom> ⇒ list<r×monom> =
  fun s x m1 l {
    let r such that x:r;
    let fn : r×monom ⇒ r×monom =
      fun c { let (y,m2) = c; (s.mul x y, mul_monom m1 m2) };
    map fn l
  }

// polynomial multiplication
val rec mul_poly : ∀r, semiring<r> ⇒ list<r×monom> ⇒ list<r×monom> ⇒ list<r×monom> =
  fun s p1 p2 {
    let r such that _:list<r×monom>;
    let fn : list<r×monom> ⇒ r×monom ⇒ list<r×monom> = fun p c {
      let (x,m) = c;
      add_poly s p (mul_monom_poly s x m p2)
    };
    fold_left fn [] p1
  }

// polynomial exponentiation
val rec exp_poly : ∀r, semiring<r> ⇒ list<r×monom> ⇒ nat ⇒ list<r×monom> =
  fun s p n {
    case n {
      Zero → (s.one,[]) :: []
      S[m] → mul_poly s p (exp_poly s p m)
    }
  }

///////////////////////////////
// evaluation of polynomials //
///////////////////////////////

val rec eval_monom : ∀r, semiring<r> ⇒ monom ⇒ (nat ⇒ r) ⇒ nat ⇒ r = fun s m env i {
  case m {
    [] → s.one
    x::m →
      let exp = exp_ring s;
      s.mul (eval_monom s m env (succ i)) (exp (env i) x)
  }
}

val rec eval : ∀x, semiring<x> ⇒ poly<x> ⇒ (nat ⇒ x) ⇒ x = fun r p env {
  case p {
    []   → r.zero
    c::p → let (x,m) = c;
           r.add (r.mul x (eval_monom r m env Zero)) (eval r p env)
  }
}

///////////////////////////////
//    polynomials as trees   //
///////////////////////////////

type rec tpoly<x> =
  [ Var of nat
  ; Cst of x
  ; Add of tpoly × tpoly
  ; Mul of tpoly × tpoly
  ; Exp of tpoly × nat
  ]

val rec var : nat ⇒ monom = fun n {
  case n {
    Zero → u1::[]
    S[p] → u0::var p
  }
}

// conversion (develop)
val rec tpoly_to_poly : ∀r, semiring<r> ⇒ tpoly<r> ⇒ list<r×monom> = fun s t {
  case t {
    Var[n]       → (s.one, var n) :: []
    Cst[x]       → (x    , []   ) :: []
    Add[(p1,p2)] → add_poly s (tpoly_to_poly s p1) (tpoly_to_poly s p2)
    Mul[(p1,p2)] → mul_poly s (tpoly_to_poly s p1) (tpoly_to_poly s p2)
    Exp[(p1,n)]  → exp_poly s (tpoly_to_poly s p1) n
  }
}

// evaluation of trees
val rec teval : ∀r, semiring<r> ⇒ tpoly<r> ⇒ (nat ⇒ r) ⇒ r = fun s t env {
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

val rec eval_monom_var : ∀r, ∀s∈semiring<r>, ∀n∈nat, ∀env∈(nat ⇒ r), ∀i∈nat,
                       eval_monom s (var n) env i ≡ env (add i n) =
  fun s n env i {
    case n {
      Zero → deduce eval_monom s (var n) env i ≡ s.mul s.one (exp_ring s (env i) u1);
             deduce exp_ring s (env i) u1 ≡ s.mul (env i) s.one;
             use s.mul_comm (env i) s.one;
             use s.mul_neutral (env i);
             deduce eval_monom s (var n) env i ≡ env i;
             use add_n_zero i;
             qed
      S[p] → deduce var n ≡ Zero :: var p;
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

val eval_var : ∀r, ∀s∈semiring<r>,  ∀n∈nat, ∀env∈(nat ⇒ r),
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

val eval_cst : ∀r, ∀s∈semiring<r>,  ∀x∈r, ∀env∈(nat ⇒ r),
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

val rec eval_add : ∀r, ∀s∈semiring<r>,  ∀p1 p2∈list<r×monom>, ∀env∈(nat ⇒ r),
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

val eval_mul : ∀r, ∀s∈semiring<r>,  ∀p1 p2∈list<r×monom>, ∀env∈(nat ⇒ r),
                  eval s (mul_poly s p1 p2) env ≡ s.mul (eval s p1 env) (eval s p2 env) =
  fun s p1 p2 env {
    {--}
  }

val eval_exp : ∀r, ∀s∈semiring<r>,  ∀p∈list<r×monom>, ∀e∈nat, ∀env∈(nat ⇒ r),
                  eval s (exp_poly s p e) env ≡ exp_ring s (eval s p env) e =
  fun s p1 p2 env {
    {--}
  }

// Main theorem
val rec eval_cor : ∀r, ∀s∈semiring<r>, ∀t∈tpoly<r>, ∀env∈(nat ⇒ r),
                teval s t env ≡ eval s (tpoly_to_poly s t) env =
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

// Test with polynomials with integer coefficients
val semi_nat : semiring<nat> = {
  zero = zero; one; add; mul;
  add_neutral = fun n { {} };
  add_assoc; add_comm;
  mul_neutral; mul_assoc; mul_comm;
  mul_distrib = mul_dist_l;
  mul_abs = fun n { {} }
}

val test1 : npoly<nat> =
    let x = Var[u0];
    let y = Var[u1];
    tpoly_to_poly semi_nat Exp[(Add[(x,y)],u2)]

val test2 : npoly<nat> =
    let x = Var[u0];
    let y = Var[u1];
    tpoly_to_poly semi_nat Mul[(Add[(x,y)],Add[(x,y)])]

val test3 : test1 ≡ test2 = qed

val test4 : npoly<nat> =
    let x = Var[u0];
    let y = Var[u1];
    tpoly_to_poly semi_nat Add[(Exp[(x,u2)],Add[(Mul[(Cst[u2],Mul[(x,y)])],Exp[(y,u2)])])]

val test5 : test1 ≡ test4 = qed

val exp : nat ⇒ nat ⇒ nat = exp_ring semi_nat

val test_binome : ∀x y∈nat, exp (add x y) u2 ≡ add (exp x u2) (add (mul u2 (mul x y)) (exp y u2)) =
  fun a b {
    let x = Var[u0];
    let y = Var[u1];
    let env : nat ⇒ nat = fun v { case v { Zero → a | S[p] → b } };
    use eval_cor semi_nat Exp[(Add[(x,y)],u2)] env;
    use eval_cor semi_nat Add[(Exp[(x,u2)],Add[(Mul[(Cst[u2],Mul[(x,y)])],Exp[(y,u2)])])] env;
    qed
  }

val test_trinome : ∀x y∈nat, exp (add x y) u3 ≡ add (exp x u3) (add (mul u3 (mul (exp x u2)  y))
                                                            (add (mul u3 (mul x (exp y u2)))
                                                                (exp y u3))) =
  fun a b {
    let x = Var[u0];
    let y = Var[u1];
    let env : nat ⇒ nat = fun v { case v { Zero → a | S[p] → b } };
    use eval_cor semi_nat Exp[(Add[(x,y)],u3)] env;
    use eval_cor semi_nat Add[(Exp[(x,u3)],Add[(Mul[(Cst[u3],Mul[(Exp[(x,u2)],y)])],
                         Add[(Mul[(Cst[u3],Mul[(x,Exp[(y,u2)])])],Exp[(y,u3)])])])] env;
    qed
  }
