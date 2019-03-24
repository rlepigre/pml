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
      Zero    → let lem = add_n_zero m; {}
      Succ[k] → let ih = add_comm k m;
                let lem = add_succ m k; {}
    }
  }

val rec add_asso : ∀n m p∈nat, add n (add m p) ≡ add (add n m) p =
  fun n m p {
    let tot_m_p = add m p;
    case n {
      Zero    → {}
      Succ[k] → let tot_k_m = add k m;
                let ih = add_asso k m p; {}
    }
  }

val rec mul_n_zero : ∀n∈nat, mul n Zero ≡ Zero =
  fun n {
    case n {
      Zero    → {}
      Succ[k] → let ih = mul_n_zero k; {}
    }
  }

val rec mul_succ : ∀n m∈nat, mul n Succ[m] ≡ add (mul n m) n =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → let lem = mul_succ k m;
                let tot = mul k m;
                let tot = add m (mul k m);
                let lem = add_succ (add m (mul k m)) k;
                let lem = add_asso m (mul k m) k;
                let tot = mul k Succ[m]; {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → let lem = mul_n_zero m; {}
      Succ[k] → let ih  = mul_comm m k;
                let lem = mul_succ m k;
                let tot = mul k m;
                let lem = add_comm (mul k m) m; {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → let ded : mul Zero m ≡ Zero = {};
                let lem : mul m Zero ≡ Zero = mul_n_zero m; {}
      Succ[k] → let ded : mul Succ[k] m ≡ add m (mul k m) = {};
                let ih  : mul k m ≡ mul m k = mul_comm k m;
                let lem : mul m Succ[k] ≡ add (mul m k) m =
                  mul_succ m k;
                let tot = mul k m;
                let lem : add (mul k m) m ≡ add m (mul k m) =
                  add_comm (mul k m) m; {}
    }
  }

def t_deduce⟨f:ο⟩ : τ = ({} : f)
def t_show⟨f:ο, p:τ⟩ : τ = (p : f)

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → t_deduce⟨mul Zero m ≡ Zero⟩;
                t_show⟨mul m Zero ≡ Zero, mul_n_zero m⟩
      Succ[k] → t_deduce⟨mul Succ[k] m ≡ add m (mul k m)⟩;
                t_show⟨mul k m ≡ mul m k, mul_comm k m⟩;
                t_show⟨mul m Succ[k] ≡ add (mul m k) m, mul_succ m k⟩;
                use mul k m;
                t_show⟨add (mul k m) m ≡ add m (mul k m)
                      , add_comm (mul k m) m⟩
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → deduce mul Zero m ≡ Zero;
                show mul m Zero ≡ Zero using mul_n_zero m
      Succ[k] → deduce mul Succ[k] m ≡ add m (mul k m);
                show mul k m ≡ mul m k using mul_comm k m;
                show mul m Succ[k] ≡ add (mul m k) m using mul_succ m k;
                use mul k m;
                show add (mul k m) m ≡ add m (mul k m)
                  using add_comm (mul k m) m
    }
  }

type rec list⟨a:ο⟩ = [Nil ; Cons of {hd : a ; tl : list⟨a⟩}]

val rec map : ∀a b:ο, (a ⇒ b) ⇒ list⟨a⟩ ⇒ list⟨b⟩ =
  fun f l {
    case l {
      Nil     → Nil
      Cons[c] → let hd = f c.hd;
                let tl = map f c.tl;
                Cons[{hd = hd ; tl = tl}]
    }
  }

val rec length : ∀a:ο, list⟨a⟩ ⇒ nat =
  fun l {
    case l { Nil → Zero | Cons[c] → Succ[length c.tl] }
  }

val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
    ∀l∈list⟨a⟩, map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun f g {
    fix map_map { fun ls {
      case ls {
        Nil     → {}
        Cons[c] → let hd = c.hd; let tl = c.tl;
                  let tgf = g (f hd);
                  let lem = f hd;
                  let lem = map f tl;
                  let ind = map_map tl; {}
      }
    }}
  }

type vec⟨a:ο, s:τ⟩ = ∃l:ι, l∈(list⟨a⟩ | length l ≡ s)

val rec app : ∀a:ο, ∀m n:ι, vec⟨a, m⟩ ⇒ vec⟨a, n⟩ ⇒ vec⟨a, add m n⟩ =
  fun l1 l2 {
    case l1 {
      Nil[_]  → l2
      Cons[c] → let _ = length c.tl;
                let r = app c.tl l2;
                Cons[{hd = c.hd; tl = r}]
    }
  }

val app3 : ∀a:ο, ∀m n p:ι, vec⟨a,m⟩ ⇒ vec⟨a,n⟩ ⇒ vec⟨a,p⟩
                           ⇒ vec⟨a, add m (add n p)⟩ =
  fun l1 l2 l3 {
    let lem = add (length l2) (length l3);
    app l1 (app l2 l3)
  }

val vec_to_list : ∀a:ο, ∀s:τ, vec⟨a,s⟩ ⇒ list⟨a⟩ = fun x { x }

type ord⟨a:ο⟩ = ∃cmp:ι,
  { cmp : cmp ∈ (a ⇒ a ⇒ bool)
  ; tot : ∀x y∈a, ∃v:ι, cmp x y ≡ v
  ; dis : ∀x y∈a, or (cmp x y) (cmp y x) ≡ true }

val rec insert : ∀a:ο, ord⟨a⟩ ⇒ a ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun o x l {
    case l {
      Nil[_]  → Cons[{hd = x; tl = Nil}]
      Cons[c] → let hd = c.hd; let tl = c.tl;
                if o.cmp x hd { Cons[{hd = x ; tl = l}] }
                else {
                  let tl = insert o x tl;
                  Cons[{hd = hd ; tl = tl}]
                }
    }
  }

val rec isort : ∀a:ο, ord⟨a⟩ ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun o l {
    case l {
      Nil[_]  → Nil
      Cons[c] → insert o c.hd (isort o c.tl)
    }
  }

val rec sorted : ∀a:ο, ∀o∈ord⟨a⟩, ∀l∈list⟨a⟩, bool =
  fun o l {
    case l {
      Nil      → true
      Cons[c1] → let hd = c1.hd; let tl = c1.tl;
                 case tl {
                   Nil      → true
                   Cons[c2] → let hd2 = c2.hd;
                              land⟨(o.cmp) hd hd2, sorted o tl⟩
                 }
    }
  }

type slist⟨a:ο,o:τ⟩ = ∃l:ι, l∈(list⟨a⟩ | sorted o l ≡ true)

val rec isorted : ∀a:ο, ∀o∈ord⟨a⟩, ∀x∈a, ∀l∈slist⟨a,o⟩,
                  sorted o (insert o x l) ≡ true =
  fun o x l {
    case l {
      Nil[_]   → {}
      Cons[c1] →
       let lem = o.tot x c1.hd;
       if o.cmp x c1.hd { {} }
       else {
         let lem = o.tot c1.hd x;
         let lem = o.dis x c1.hd;
         case c1.tl {
           Nil[_]   → {}
           Cons[c2] →
             let lem = insert o x c2.tl;
             let lem = o.tot c1.hd c2.hd;
             let lem = o.tot x c2.hd;
             if o.cmp c1.hd c2.hd {
               let lem = isorted o x c1.tl;
               if o.cmp x c2.hd { {} } else { {} }
             } else { ✂ }
         }
       }
    }
  }

val rec isort_sorted : ∀a:ο, ∀o∈ord⟨a⟩, ∀l∈list⟨a⟩,
                       sorted o (isort o l) ≡ true =
  fun o l {
    case l {
      | Nil[_]  → {}
      | Cons[c] → let lem = isort o c.tl;
                   let ind = isort_sorted o c.tl;
                   let lem = isorted o c.hd (isort o c.tl); {}
    }
  }

val isort_full : ∀a:ο, ∀o∈ord⟨a⟩, list⟨a⟩ ⇒ slist⟨a,o⟩ =
  fun o l {
    let tot = isort o l;
    let lem = isort_sorted o l;
    isort o l
  }

val rec exists : ∀a, (a ⇒ bool) ⇒ list⟨a⟩ ⇒ bool =
  fun pred l {
    case l {
      Nil     → false
      Cons[c] → if pred c.hd { true } else { exists pred c.tl }
    }
  }

type bot = ∀x, x
type neg⟨a⟩ = a → bot

val rec find : ∀a:ο, ∀pred∈(a ⇒ bool),
               ∀l∈list⟨a⟩, neg⟨exists pred l ≡ false⟩ → a =
  fun pred l exc {
    case l {
      Nil[_]  → exc {}
      Cons[c] → if pred c.hd { c.hd } else { find pred c.tl exc }
    }
  }

val find_opt : ∀a:ο, ∀pred∈(a ⇒ bool),
               list⟨a⟩ → option⟨a⟩ =
  fun pred l {
    save a {
      some (find pred l (fun _ { restore a none}))
    }
  }

val rec find_list : ∀a:ο, ∀pred∈(a ⇒ bool),
                    list⟨list⟨a⟩⟩ → option⟨a⟩ =
  fun pred l {
    case l {
      Nil     → none
      Cons[c] →
        save a {
          some (find pred c.hd (fun _ {
              restore a (find_list pred c.tl)
            }))
        }
    }
  }
