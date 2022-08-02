include lib.either
include lib.bool
include lib.nat
include lib.nat_proofs

//ACG with only one kind of arrow. All may be classical,
//equivalence proof in extensionality and existence of the initial witness

val chi :   ∀a,∀x∈a, ∃n, n∈nat | ψ⟨n⟩ ≡ x = χ
// Clock can be realised:
// consider (psi⟨n⟩,phi⟨n⟩) an enumération of all pairs of values.
// take v ∈ |∃x∈a, f⟨x⟩|
// by definition, there is w such that (w,v) ∈ a × f⟨w⟩.
// take n such that (psi⟨n⟩,phi⟨n⟩) = (w, v).
// We have (n, (psi⟨n⟩,psi⟨n⟩)) ∈ ∃n∈nat, psi⟨n⟩∈a × f⟨psi⟨n⟩⟩.
//
// Remark, n can be chosen using the "clock", as the
// enumeration can be build after running the program and it
// only need to be surjective.

def equiv⟨a,f,g⟩ = (∀x:ι, x∈a → f⟨x⟩ → g⟨x⟩) × (∀x:ι, x∈a → g⟨x⟩ → f⟨x⟩)

def idt : ι = fun x {x}

val eq_refl : ∀a,∀f, equiv⟨a,f,f⟩ = (fun _ {idt}, fun _ {idt})

val eq_symm : ∀a, ∀f g, equiv⟨a,f,g⟩ → equiv⟨a,g,f⟩
               = fun e { (e.2, e.1) }

val eq_tran : ∀a, ∀f g h, equiv⟨a,f,g⟩ → equiv⟨a,g,h⟩ → equiv⟨a,f,h⟩
  = fun e1 e2 { ( fun x p { e2.1 x (e1.1 x p) }
                , fun x p { e1.2 x (e2.2 x p) }) }

val rec leq_size : ∀o, ∀m∈nat^(o+ₒ1), ∀n∈nat, either⟨leq m n, n∈nat^o⟩ =
  fun m n {
    case m {
      Zero → case n {
          Zero → InL
          S[n] → InL
        }
      S[m] →
        case n {
          Zero → InR[Zero]
          S[n] →
            case m {  // case for n because leq use compare
              Zero  → case n { Zero → InL | S[_] → InL}
              S[m'] →
                case leq_size S[m'] n {
                  InL    → InL
                  InR[p] → InR[S[p]]
                  }
              }
          }
      }
  }

def mini⟨a,f:ι→ο,n:ι⟩ = ∀h,∀p:ι, p∈nat → equiv⟨a,f,h⟩ → ψ⟨p⟩∈a → h⟨ψ⟨p⟩⟩ → n ≤ p
def best⟨a,f:ι→ο,g:ι→ο,n:ι⟩ = n ∈ nat × equiv⟨a,f,g⟩ × ψ⟨n⟩∈a × g⟨ψ⟨n⟩⟩ × mini⟨a,f,n⟩

val ac1
  : ∀a,∀f:ι→ο, (∃x∈a, f⟨x⟩) → ∃g,∃n:ι, best⟨a,f,g,n⟩
  = fun h {
    let a,f such that h : ∃x∈a, f⟨x⟩;
    let (x,p) = h;
    let n : ∃n, n∈nat | ψ⟨n⟩ ≡ x = χ x;
    save s {
      let rec fn : ∀g,∀n:ι, n∈nat → equiv⟨a,f,g⟩ → ψ⟨n⟩∈a → g⟨ψ⟨n⟩⟩ →
               ∃n, best⟨a,f,g,n⟩
        = fun n e x h {
            let o such that n : nat^(o+ₒ1);
            (n, e, x, h,
                fun p e x h {
                  case leq_size (n:nat^(o+ₒ1)) p {
                    InL → qed
                    InR[p] → restore s (fn p e x h)
                  }
                })
        };
      fn n eq_refl x p
    }
  }

def choice⟨a,f,x⟩ = ∃n:ι, n ∈ nat × ψ⟨n⟩ ∈ a × f⟨ψ⟨n⟩⟩ × mini⟨a,f,n⟩ | x ≡ ψ⟨n⟩

val mk_choice : ∀a,∀f, (∃x∈a, f⟨x⟩) → ∃x, choice⟨a,f,x⟩
    = fun v {
        let c = ac1 v;
        let a,f,g,n such that c : best⟨a,f,g,n⟩;
        let c : best⟨a,f,g,n⟩ = c;
        (c.1, c.3, c.2.2 c.3 c.4, c.5)
    }

val choice_correct : ∀a,∀f:ι→ο,∀x:ι, choice⟨a,f,x⟩ → x ∈ a × f⟨x⟩
   = fun c { (c.2, c.3) }

val choice_unique
       : ∀a,∀f g,∀x y, choice⟨a,f,x⟩ → choice⟨a,g,y⟩ →
                       equiv⟨a,f,g⟩ → x ≡ y
   = fun c1 c2 eq {
       let p1 = c1.4 c2.1 eq c2.2 c2.3;
       let p2 = c2.4 c1.1 (eq_symm eq) c1.2 c1.3;
       show c1.1 ≡ c2.1 using leq_anti c1.1 c2.1 p1 p2;
       qed
   }


// Construction des quotients version avec bool
type eq_rel⟨a,eq⟩ =  { r : ∀x:ι, x∈a → eq⟨x, x⟩
                    ; s : ∀x y:ι, x∈a → y∈a → eq⟨x, y⟩ → eq⟨y, x⟩
                    ; t : ∀x y z:ι, x∈a → y∈a → z∈a → eq⟨x, y⟩ → eq⟨y, z⟩ → eq⟨x, z⟩ }

type class⟨a,eq:ι→ι→ο,x:ι,y:ι⟩ = choice⟨a, (z:ι ↦ (eq⟨x,z⟩)), y⟩

val mk_class : ∀a,∀eq:ι→ι→ο, eq_rel⟨a,eq⟩ → ∀x:ι, (x∈a → ∃y:ι, class⟨a,eq,x,y⟩)
   = fun e x {
       let a, eq such that e:eq_rel⟨a,eq⟩;
       mk_choice ((x, e.r x) : ∃z∈a, eq⟨x, z⟩)
   }

val class_equal :
   ∀a,∀eq:ι→ι→ο, eq_rel⟨a,eq⟩ → ∀x_1 y_1 x_2 y_2:ι, x_1 ∈ a → x_2 ∈ a →
      class⟨a,eq,x_1,y_1⟩→  class⟨a,eq,x_2,y_2⟩ →
       eq⟨x_1, x_2⟩ → y_1 ≡ y_2
     = fun e x_1 x_2 c_1 c_2 ee {
         let a, eq such that e:eq_rel⟨a,eq⟩;
         let p : equiv⟨a,(z:ι ↦ (eq⟨x_1, z⟩)),(z:ι ↦ (eq⟨x_2, z⟩))⟩ =
           (fun z p { e.t x_2 x_1 z (e.s x_1 x_2 ee) p }
           ,fun z p { e.t x_1 x_2 z ee p});
         choice_unique c_1 c_2 p
     }

val class_correct :
   ∀a,∀eq:ι→ι→ο, eq_rel⟨a,eq⟩ → ∀x y:ι, x∈a →
      class⟨a,eq,x,y⟩ → y ∈ a × eq⟨x, y⟩
         = fun e x c { (c.2, c.3) }

def mini2⟨a,x:ι,n:ι⟩ = (∀p:ι, p∈nat | ψ⟨p⟩ ≡ x → n ≤ p)
def index⟨a,x:ι,n:ι⟩ = n ∈ nat | ψ⟨n⟩ ≡ x × mini2⟨a,x,n⟩

val index_exists
  : ∀a,∀x:ι,x ∈ a → ∃n:ι, index⟨a,x,n⟩
  = fun x {
    let a such that x : a;
    let n : ∃n, n∈nat | ψ⟨n⟩ ≡ x = χ x;
    save s {
      let rec fn : ∀n:ι, n∈nat | ψ⟨n⟩≡x → ∃n, index⟨a,x,n⟩
        = fun n {
            let o such that n : nat^(o+ₒ1);
            (n, fun p {
                  case leq_size (n:nat^(o+ₒ1)) p {
                    InL → qed
                    InR[p] → restore s (fn p)
                  }
                })
        };
      fn n
    }
  }

val index_unique
  : ∀a, ∀x n m:ι, index⟨a,x,n⟩ → index⟨a,x,m⟩ → n ≡ m
  = fun xi yi {
      let n = xi.1; let m = yi.1;
      let ineq1 : n ≤ m = xi.2 m;
      let ineq2 : m ≤ n = yi.2 n;
      use leq_anti n m ineq1 ineq2;
      qed
  }

type le⟨a,x,y⟩ = ∃n m:ι, index⟨a,x,n⟩ × index⟨a,y,m⟩ × n < m

val le_total : ∀a, ∀x y:ι, x∈a → y∈a → either⟨x ≡ y, either⟨le⟨a,x,y⟩,le⟨a,y,x⟩⟩⟩
  = fun x y {
    let a such that x : a;
    let ix = index_exists x;
    let iy = index_exists y;
    case compare ix.1 iy.1 {
      Eq → InL
      Ls → InR[InL[(ix,iy,{})]]
      Gr → InR[InR[(iy,ix,lt_gt iy.1 ix.1)]]
    }
  }

val reduce_size : ∀o, ∀n∈nat^(o+ₒ1), ∀m∈nat | m < n, m ∈ nat^o =
  fun n m {
    let o such that n : nat^(o+ₒ1);
    check {
      case leq_size (n : nat^(o+ₒ1)) m {
        InL    → show not (m < n) by leq_lt n m;
                 ✂
        InR[p] → p
      }}
    for m
  }

val le_well_founded : ∀a, ∀p, (∀x:ι, (∀y:ι, y∈a → le⟨a,y,x⟩ → p⟨y⟩) → x∈a → p⟨x⟩)
                               → ∀x:ι, x∈a → p⟨x⟩ =
   fun ind x0 {
    let a such that x0 : x0 ∈ a;
    let p such that _ : p⟨x0⟩;
    let ind : ∀x:ι, (∀y:ι, y∈a → le⟨a,y,x⟩ → p⟨y⟩) → x∈a → p⟨x⟩ = ind;
    let rec fn : ∀x:ι, ∀n:ι, x ∈ a → index⟨a,x,n⟩ → n ∈ nat → p⟨x⟩ =
      fun x ix n {
        deduce n ≡ ix.1;
        let o such that n : nat^(o+ₒ1);
        let gn : ∀y:ι, y∈a → le⟨a,y,x⟩ → p⟨y⟩ =
          fun y le {
            let iy = le.1;
            let ix' = le.2;
            let _ : n ≡ ix'.1 = index_unique ix ix';
            deduce iy.1 < n;
            let p = reduce_size (n : nat^(o+ₒ1)) iy.1;
            fn y (p, iy.2) p
          };
        ind gn x
      };
    let ix = index_exists x0;
    fn x0 ix ix.1
   }
