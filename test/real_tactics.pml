include lib.bool
include lib.option

type rec nat = [Zero ; Succ of nat]

val rec add : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero    → m
      Succ[k] → Succ[add k m]
    }
  }

val rec mul : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero    → Zero
      Succ[k] → add m (mul k m)
    }
  }

val add_zero_v : ∀v:ι,   add Zero v ≡ v    = {}
val mul_zero_v : ∀v:ι,   mul Zero v ≡ Zero = {}
val add_zero_n : ∀n∈nat, add Zero n ≡ n    = fun _ { {} }
val mul_zero_n : ∀n∈nat, mul Zero n ≡ Zero = fun _ { {} }

val rec add_n_zero : ∀n∈nat, add n Zero ≡ n =
  fun n {
    case n {
      Zero    → {}
      Succ[k] → add_n_zero k
    }
  }

val rec add_succ : ∀n m∈nat, add n Succ[m] ≡ Succ[add n m] =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → add_succ k m
    }
  }

val rec add_comm : ∀n m∈nat, add n m ≡ add m n =
  fun n m {
    case n {
      Zero    → let lem = add_n_zero m in {}
      Succ[k] → let ih = add_comm k m in
                let lem = add_succ m k in {}
    }
  }

val rec add_total : ∀n m∈nat, ∃v:ι, add n m ≡ v =
  fun n m {
    case n {
      Zero[_] → {}
      Succ[k] → add_total k m
    }
  }

val rec add_asso : ∀n m p∈nat, add n (add m p) ≡ add (add n m) p =
  fun n m p {
    let tot_m_p = add_total m p in
    case n {
      Zero    → {}
      Succ[k] → let tot_k_m = add_total k m in
                let ih = add_asso k m p in {}
    }
  }

val rec mul_n_zero : ∀n∈nat, mul n Zero ≡ Zero =
  fun n {
    case n {
      Zero    → {}
      Succ[k] → let ih = mul_n_zero k in {}
    }
  }

val rec mul_total : ∀n m∈nat, ∃v:ι, mul n m ≡ v =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → let ih = mul_total k m in
                let lem = add_total m (mul k m) in {}
    }
  }

val rec mul_succ : ∀n m∈nat, mul n Succ[m] ≡ add (mul n m) n =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → let lem = mul_succ k m in
                let tot = mul_total k m in
                let tot = add_total m (mul k m) in
                let lem = add_succ (add m (mul k m)) k in
                let lem = add_asso m (mul k m) k in
                let tot = mul_total k Succ[m] in {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → let lem = mul_n_zero m in {}
      Succ[k] → let ih  = mul_comm m k in
                let lem = mul_succ m k in
                let tot = mul_total k m in
                let lem = add_comm (mul k m) m in {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → let ded : mul Zero m ≡ Zero = {} in
                let lem : mul m Zero ≡ Zero = mul_n_zero m in {}
      Succ[k] → let ded : mul Succ[k] m ≡ add m (mul k m) = {} in
                let ih  : mul k m ≡ mul m k = mul_comm k m in
                let lem : mul m Succ[k] ≡ add (mul m k) m =
                  mul_succ m k
                in
                let tot : (∃v:ι, mul k m ≡ v) = mul_total k m in
                let lem : add (mul k m) m ≡ add m (mul k m) =
                  add_comm (mul k m) m
                in {}
    }
  }

def t_deduce<f:ο> : τ = ({} : f)
def t_show<f:ο, p:τ> : τ = (p : f)

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → t_deduce<mul Zero m ≡ Zero>;
                t_show<mul m Zero ≡ Zero, mul_n_zero m>
      Succ[k] → t_deduce<mul Succ[k] m ≡ add m (mul k m)>;
                t_show<mul k m ≡ mul m k, mul_comm k m>;
                t_show<mul m Succ[k] ≡ add (mul m k) m, mul_succ m k>;
                t_show<(∃v:ι, mul k m ≡ v), mul_total k m>;
                t_show<add (mul k m) m ≡ add m (mul k m)
                      , add_comm (mul k m) m>
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → deduce mul Zero m ≡ Zero;
                show mul m Zero ≡ Zero using mul_n_zero m
    | Succ[k] → deduce mul Succ[k] m ≡ add m (mul k m); // FIXME syntax bug
                show mul k m ≡ mul m k using mul_comm k m;
                show mul m Succ[k] ≡ add (mul m k) m using mul_succ m k;
                show ∃v:ι, mul k m ≡ v using mul_total k m;
                show add (mul k m) m ≡ add m (mul k m)
                using add_comm (mul k m) m
    }
  }

type rec list<a:ο> = [Nil ; Cons of {hd : a ; tl : list}]

val rec map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> =
  fun f l {
    case l {
      Nil     → Nil
      Cons[c] → let hd = f c.hd in
                let tl = map f c.tl in
                Cons[{hd = hd ; tl = tl}]
    }
  }

val rec length : ∀a:ο, list<a> ⇒ nat =
  fun l {
    case l { Nil → Zero | Cons[c] → Succ[length c.tl] }
  }

// total<f,a> means that f is total on the domain a.
def total<f:ι,a:ο> : ο = ∀x∈a, ∃v:ι, f x ≡ v

val rec map_total : ∀a b:ο, ∀f∈(a ⇒ b), total<f,a>
                    ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
  fun fn ft ls {
    case ls {
      Nil[_]  → {}
      Cons[c] → let lem = ft c.hd in
                let ih  = map_total fn ft c.tl in {}
    }
  }

val rec length_total : ∀a:ο, ∀l∈list<a>, ∃v:ι, v ≡ length l =
  fun l {
    case l {
      Nil[_]  → {}
      Cons[c] → let ind = length_total c.tl in {}
    }
  }

val compose_total : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
                    total<f,a> ⇒ total<g,b> ⇒
                    total<(fun x { g (f x) }), a> =
  fun f g ftot gtot a {
    let lem = ftot a in
    let lem = gtot (f a) in {}
  }

val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
    total<f,a> ⇒ total<g,b> ⇒
    ∀l∈list<a>, map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun f g ftot gtot {
    fix fun map_map ls {
      case ls {
        Nil     → {}
        Cons[c] → let hd = c.hd in let tl = c.tl in
                  let tgf = compose_total f g ftot gtot hd in
                  let lem = ftot hd in
                  let lem = map_total f ftot tl in
                  let ind = map_map tl in {}
      }
    }
  }

type vec<a:ο, s:τ> = ∃l:ι, l∈(list<a> | length l ≡ s)

val rec app : ∀a:ο, ∀m n:ι, vec<a, m> ⇒ vec<a, n> ⇒ vec<a, add m n> =
  fun l1 l2 {
    case l1 {
      Nil[_]  → l2
      Cons[c] → let _ = length_total c.tl in
                let r = app c.tl l2 in
                Cons[{hd = c.hd; tl = r}]
    }
  }

val app3 : ∀a:ο, ∀m n p:ι, vec<a,m> ⇒ vec<a,n> ⇒ vec<a,p>
                           ⇒ vec<a, add m (add n p)> =
  fun l1 l2 l3 {
    let lem = add_total (length l2) (length l3) in
    app l1 (app l2 l3)
  }

val vec_to_list : ∀a:ο, ∀s:τ, vec<a,s> ⇒ list<a> = fun x { x }

type ord<a:ο> = ∃cmp:ι,
  { cmp : cmp ∈ (a ⇒ a ⇒ bool)
  ; tot : ∀x y∈a, ∃v:ι, cmp x y ≡ v
  ; dis : ∀x y∈a, or (cmp x y) (cmp y x) ≡ true }

val rec insert : ∀a:ο, ord<a> ⇒ a ⇒ list<a> ⇒ list<a> =
  fun o x l {
    case l {
      Nil[_]  → Cons[{hd = x; tl = Nil}]
      Cons[c] → let hd = c.hd in let tl = c.tl in
                if o.cmp x hd {
                  Cons[{hd = x ; tl = l}]
                } else {
                  let tl = insert o x tl in
                  Cons[{hd = hd ; tl = tl}]
                }
    }
  }

val rec isort : ∀a:ο, ord<a> ⇒ list<a> ⇒ list<a> =
  fun o l {
    case l {
      Nil[_]  → Nil
      Cons[c] → insert o c.hd (isort o c.tl)
    }
  }

val rec sorted : ∀a:ο, ∀o∈ord<a>, ∀l∈list<a>, bool =
  fun o l {
    case l {
      Nil      → true
      Cons[c1] → let hd = c1.hd in let tl = c1.tl in
                 case tl {
                   Nil      → true
                   Cons[c2] → let hd2 = c2.hd in
                              land<(o.cmp) hd hd2, sorted o tl>
                 }
    }
  }

type slist<a:ο,o:τ> = ∃l:ι, l∈(list<a> | sorted o l ≡ true)

val rec insert_total : ∀a:ο, ∀o∈ord<a>, ∀x∈a, ∀l∈list<a>,
                       ∃v:ι, insert o x l ≡ v =
  fun o x l {
    case l {
      Nil      → {}
      Cons[c1] → let hd = c1.hd in let tl = c1.tl in
                 let lem = o.tot x hd in
                 if o.cmp x hd { {} }
                 else { let ih = insert_total o x tl in {} }
    }
  }

val rec isort_total :  ∀a:ο, ∀o∈ord<a>, ∀l∈list<a>,
                       ∃v:ι, isort o l ≡ v =
  fun o l {
    case l {
      Nil[_]  → {}
      Cons[c] → let ih  = isort_total o c.tl in
                let lem = insert_total o c.hd (isort o c.tl) in {}
    }
  }

val rec isorted : ∀a:ο, ∀o∈ord<a>, ∀x∈a, ∀l∈slist<a,o>,
                  sorted o (insert o x l) ≡ true =
  fun o x l {
    case l {
      Nil[_]   → {}
      Cons[c1] →
       let lem = o.tot x c1.hd in
       if o.cmp x c1.hd { {} }
       else {
         let lem = o.tot c1.hd x in
         let lem = o.dis x c1.hd in
         case c1.tl {
           Nil[_]   → {}
           Cons[c2] →
             let lem = insert_total o x c2.tl in
             let lem = o.tot c1.hd c2.hd in
             let lem = o.tot x c2.hd in
             if o.cmp c1.hd c2.hd {
               let lem = isorted o x c1.tl in
               if o.cmp x c2.hd { {} } else { {} }
             } else {
               ✂
             }
         }
       }
    }
  }

val rec isort_sorted : ∀a:ο, ∀o∈ord<a>, ∀l∈list<a>,
                       sorted o (isort o l) ≡ true =
  fun o l {
    case l {
      | Nil[_]  → {}
      | Cons[c] → let lem = isort_total o c.tl in
                   let ind = isort_sorted o c.tl in
                   let lem = isorted o c.hd (isort o c.tl) in {}
    }
  }

val isort_full : ∀a:ο, ∀o∈ord<a>, list<a> ⇒ slist<a,o> =
  fun o l {
    let tot = isort_total o l in
    let lem = isort_sorted o l in
    isort o l
  }

val rec exists : ∀a, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun pred l {
    case l {
      Nil     → false
      Cons[c] → if pred c.hd { true } else { exists pred c.tl }
    }
  }

type bot = ∀x, x
type neg<a> = a ⇒ bot

val rec find : ∀a:ο, ∀pred∈(a ⇒ bool), total<pred,a> ⇒
               ∀l∈list<a>, neg<exists pred l ≡ false> ⇒ a =
  fun pred pred_tot l exc {
    case l {
      Nil[_]  → exc {}
      Cons[c] → let lem = pred_tot c.hd in
                if pred c.hd { c.hd }
                else { find pred pred_tot c.tl exc }
    }
  }

val find_opt : ∀a:ο, ∀pred∈(a ⇒ bool), total<pred,a> ⇒
               list<a> ⇒ option<a> =
  fun pred pred_tot l {
    save a {
      some (find pred pred_tot l (fun _ { restore a none}))
    }
  }

val rec find_list : ∀a:ο, ∀pred∈(a ⇒ bool), total<pred,a> ⇒
                    list<list<a>> ⇒ option<a> =
  fun pred pred_tot l {
    case l {
      Nil     → none
      Cons[c] →
        save a {
          some (find pred pred_tot c.hd (fun _ { 
              restore a (find_list pred pred_tot c.tl)
            }))
        }
    }
  }
