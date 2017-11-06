include lib.bool
include lib.nat

type rec tree23<a:ο> = [
  E ;
  N2 of { l : tree23; x : a; r : tree23 } ;
  N3 of { l : tree23; x : a; m : tree23; y : a; r : tree23 } ]

type cmp = [ Le ; Eq ; Ge ]

val rec mem : ∀a:ο, (a⇒a⇒cmp) ⇒ a => tree23<a> => bool =
  fun f z t {
    case t {
      E     → false
      N2[{l; x; r}] →
        case f z x { Le → mem f z l | Eq → true | Ge → mem f z r }
      N3[{l; x; m; y; r}] →
        case f z x { Le → mem f z l | Eq → true | Ge →
          case f z y { Le → mem f z m | Eq → true | Ge → mem f z r }
        }
    }
  }

def cmp_total<f,a:ο> = ∀x y∈a, ∃v:ι, f x y ≡ v

val mem_total : ∀a:ο, ∀f∈(a⇒a⇒cmp), cmp_total<f,a> ⇒ ∀x∈a, ∀t∈tree23<a>,
      ∃v:ι, mem f x t ≡ v =
  fun f ft z {
    fix fun mem_total t {
      case t {
        E     → {}
        N2[{l; x; r}] →
          let _ = ft z x;
          case f z x { Le → mem_total l | Eq → {} | Ge → mem_total r }
        N3[{l; x; m; y; r}] →
          let _ = ft z x;
          case f z x { Le → mem_total l | Eq → {} | Ge →
            let _ = ft z y;
            case f z y { Le → mem_total m | Eq → {} | Ge → mem_total r }
        }
      }
    }
  }

type add23<a:ο> = [
  N1 of tree23<a> ;
  N2 of { l : tree23<a>; x : a; r : tree23<a> } ]

val rec add_aux : ∀a:ο, (a⇒a⇒cmp) ⇒ a ⇒ tree23<a> ⇒ add23<a> =
  fun f x t {
    case t {
    | E     → N2[{l=E; x=x; r=E}]
    | N2[c] →
       case f x c.x {
       | Le → case add_aux f x c.l {
              | N1[t] → N1[N2[{l=t;x=c.x;r=c.r}]]
              | N2[n] → N1[N3[{l=n.l;x=n.x;m=n.r;y=c.x;r=c.r}]]
              }
       | Eq → N1[t]
       | Ge → case add_aux f x c.r {
              | N1[t] → N1[N2[{l=c.l;x=c.x;r=t}]]
              | N2[n] → N1[N3[{l=c.l;x=c.x;m=n.l;y=n.x;r=n.r}]]
              }}
    | N3[c] →
       case f x c.x {
       | Le → case add_aux f x c.l {
              | N1[t] → N1[N3[{l=t;x=c.x;m=c.m;y=c.y;r=c.r}]]
              | N2[n] → N2[{l=N2[{l=n.l;x=n.x;r=n.r}]
                           ;x=c.x
                           ;r=N2[{l=c.m;x=c.y;r=c.r}]}]
              }
       | Eq → N1[t]
       | Ge →
       case f x c.y {
       | Le → case add_aux f x c.m {
              | N1[t] → N1[N3[{l=c.l;x=c.x;m=t;y=c.y;r=c.r}]]
              | N2[n] → N2[{l=N2[{l=c.l;x=c.x;r=n.l}]
                           ;x=n.x
                           ;r=N2[{l=n.r;x=c.y;r=c.r}]}]
              }
       | Eq → N1[t]
       | Ge → case add_aux f x c.r {
              | N1[t] → N1[N3[{l=c.l;x=c.x;m=t;y=c.y;r=c.r}]]
              | N2[n] → N2[{l=N2[{l=c.l;x=c.x;r=c.m}]
                           ;x=c.y
                           ;r=N2[{l=n.l;x=n.x;r=n.r}]}]
              }}}
    }
  }

val add : ∀a:ο, (a⇒a⇒cmp) ⇒ a ⇒ tree23<a> ⇒ tree23<a> =
  fun f x t {
    case add_aux f x t {
      N1[u] → u
      N2[c] → N2[c]
    }
  }

val add_aux_total : ∀a:ο, ∀f∈(a⇒a⇒cmp), cmp_total<f,a> ⇒ ∀x∈a,
                    ∀t∈tree23<a>, ∃v:ι, (add_aux f x t) ≡ v =
  fun f ft x {
    fix fun add_aux_total t {
      case t {
      | E     → {}
      | N2[c] →
         let _ = ft x c.x;
         case f x c.x {
         | Le → let lem = add_aux_total c.l;
                case add_aux f x c.l {
                | N1[t] → {}
                | N2[n] → {}
                }
         | Eq → {}
         | Ge → let lem = add_aux_total c.r;
                case add_aux f x c.r {
                | N1[t] → {}
                | N2[n] → {}
                }}
      | N3[c] →
         let _ = ft x c.x;
         case f x c.x {
         | Le → let lem = add_aux_total c.l;
                case add_aux f x c.l {
                | N1[t] → {}
                | N2[n] → {}
                }
         | Eq → {}
         | Ge →
         let _ = ft x c.y;
         case f x c.y {
         | Le → let lem = add_aux_total c.m;
                case add_aux f x c.m {
                | N1[t] → {}
                | N2[n] → {}
                }
         | Eq → {}
         | Ge → let lem = add_aux_total c.r;
                case add_aux f x c.r {
                | N1[t] → {}
                | N2[n] → {}
                }}}
      }
    }
  }

val add_total : ∀a:ο, ∀f∈(a⇒a⇒cmp), cmp_total<f,a> ⇒
                ∀x∈a, ∀t∈tree23<a>, ∃v:ι, add f x t ≡ v =
  fun f ft x t {
    let _ = add_aux_total f ft x t;
    case add_aux f x t {
      N1[u] → {}
      N2[c] → {}
    }
  }

val mem_aux : ∀a:ο, (a⇒a⇒cmp) ⇒ a => add23<a> => bool =
  fun f x t {
    case t {
      N1[u] → mem f x u
      N2[c] → mem f x N2[c]
    }
  }

val rec height : ∀a:ο, tree23<a> ⇒ nat ⇒ bool =
  fun t n {
    case n {
    | Zero →
      case t {
      | E     → true
      | N2[_] → false
      | N3[_] → false }
    | S[p] →
      case t {
      | E     → false
      | N2[c] → and (height c.l p) (height c.r p)
      | N3[c] → and (height c.l p) (and (height c.m p) (height c.r p)) }
    }
  }

val rec height_total : ∀a:ο, ∀t∈tree23<a>, ∀n∈nat, ∃v:ι, height t n ≡ v =
  fun t n {
    case n {
    | Zero →
      case t {
      | E     → {}
      | N2[_] → {}
      | N3[_] → {} }
    | S[p] →
      case t {
      | E     → {}
      | N2[c] → let _ = height_total c.l p;
                let _ = height_total c.r p;
                cond<height c.l p,{},{}>
      | N3[c] → let _ = height_total c.l p;
                let _ = height_total c.m p;
                let _ = height_total c.r p;
                if height c.l p { cond<height c.m p,{},{}> }
                else { cond<height c.m p,{},{}> }
      }
    }
  }

val height_aux : ∀a:ο, add23<a> ⇒ nat ⇒ bool =
  fun t n {
    case t {
      N1[u] → height u n
      N2[c] → and (height c.l n) (height c.r n)
    }
  }

val and_left : ∀b1 b2∈bool, and b1 b2 ≡ true ⇒ b1 ≡ true =
  fun b1 b2 _ { cond<b1,{},✂> }

val and_right : ∀b1 b2∈bool, and b1 b2 ≡ true ⇒ b2 ≡ true =
  fun b1 b2 _ { and_left b1 b2 {} }

val and_total : ∀b1 b2∈bool, ∃v:ι, and b1 b2 ≡ v =
  fun b1 b2 { cond<b1,{},{}> }

val add_height_aux : ∀a:ο, ∀f∈(a⇒a⇒cmp), cmp_total<f,a> ⇒ ∀x∈a, ∀n∈nat,
                     ∀t∈(tree23<a> | height t n ≡ true),
                     height_aux (add_aux f x t) n ≡ true =
  fun f ft x {
    fix fun add_height_aux n t {
      case t {
      | E     → {}
      | N2[c] →
         let _ = ft x c.x;
         case n { Zero → ✂ | S[p] →
         let _ = height_total c.l p;
         let _ = height_total c.r p;
         let _ = height_total t n;
         let _ = and_left (height c.l p) (height c.r p) {};
         (case f x c.x {
         | Le → let _ = add_aux_total f ft x c.l;
                let _ = add_height_aux p c.l;
                case add_aux f x c.l {
                | N1[t] → {}
                | N2[n] → let _ = height_total n.l p;
                          let _ = height_total n.r p;
                          let _ = and_left (height n.l p) (height n.r p) {};
                          {}
                }
         | Eq → {}
         | Ge → let _ = add_aux_total f ft x c.r;
                let _ = add_height_aux p c.r;
                case add_aux f x c.r {
                | N1[t] → {}
                | N2[n] → {}
                }
         })}
      | N3[c] →
         let _ = ft x c.x;
         let _ = ft x c.y;
         case n { Zero → ✂ | S[p] →
         let _ = height_total c.l p;
         let _ = height_total c.m p;
         let _ = height_total c.r p;
         let _ = height_total t n;
         let _ = and_total (height c.m p) (height c.r p);
         let _ = and_left (height c.l p) (and (height c.m p) (height c.r p)) {};
         let _ = and_left (height c.m p) (height c.r p) {};
         case f x c.x {
         | Le → let _ = add_aux_total f ft x c.l;
                let _ = add_height_aux p c.l;
                case add_aux f x c.l {
                | N1[t] → {}
                | N2[n] → let _ = height_total n.l p;
                          let _ = height_total n.r p;
                          let _ = and_left (height n.l p) (height n.r p) {};
                          {}
                }
         | Eq → {}
         | Ge →
         case f x c.y {
         | Le → let _ = add_aux_total f ft x c.m;
                let _ = add_height_aux p c.m;
                case add_aux f x c.m {
                | N1[t] → {}
                | N2[n] → let _ = height_total n.l p;
                          let _ = height_total n.r p;
                          let _ = and_left (height n.l p) (height n.r p) {};
                          {}
                }
         | Eq → {}
         | Ge → let _ = add_aux_total f ft x c.r;
                let _ = add_height_aux p c.r;
                case add_aux f x c.r {
                | N1[t] → {}
                | N2[n] → {}
                }}}}
      }
    }
  }

val add_height : ∀a:ο, ∀f∈(a⇒a⇒cmp), cmp_total<f,a> ⇒ ∀x∈a, ∀n∈nat,
                 ∀t∈(tree23<a> | height t n ≡ true),
                 or (height (add f x t) n) (height (add f x t) S[n]) ≡ true =
  fun f ft x n t {
    let _ = add_height_aux f ft x n t;
    let _ = add_total f ft x t;
    let _ = add_aux_total f ft x t;
    let _ = height_total (add f x t) n;
    let _ = height_total (add f x t) S[n];
    case add_aux f x t {
      N1[u] → {}
      N2[c] → cond<height (add f x t) n,{},{}>
    }
  }

type bal23<a:ο> = ∃t n:ι, t ∈ tree23<a> | height t n ≡ true
