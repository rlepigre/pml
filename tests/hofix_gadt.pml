
type rec triangle⟨a⟩ =  [ Nil ; Cns of a × triangle⟨triangle⟨a⟩⟩ ]

val x : ∀a, triangle⟨a⟩ = Nil

val cns : ∀a, a ⇒ triangle⟨triangle⟨a⟩⟩ ⇒ triangle⟨a⟩
        = fun a l { Cns[(a, l)] }

val rec map : ∀a b, (a ⇒ b) ⇒ triangle⟨a⟩ ⇒ triangle⟨b⟩
  = fun f l {
    case l {
      Nil → Nil
      Cns[(a,l)] → Cns[(f a, map (map f) l)]
    }
  }

include lib.nat

type rec slist⟨a,n:τ⟩ =
  [ Nil of {} | n ≡ Zero
  ; Cons of ∃p:ι, { hd : a; tl : slist⟨a,p⟩ } | n ≡ succ p ]

val nil : ∀a, slist⟨a,zero⟩ = Nil

val cons : ∀a, ∀p:ι, a ⇒ slist⟨a,p⟩ ⇒ slist⟨a,succ p⟩ =
  fun a l { Cons[{ hd = a; tl = l}] }

val rec length : ∀a:ο,∀n:τ, slist⟨a,n⟩ ⇒ n ∈ nat  =
  fun l {
    case l {
      []    → zero
      _::tl → succ (length tl)
    }
  }


val up : ∀o, ∀a, ∀n:ι, slist^o⟨a,n⟩ ⇒ slist⟨a,n⟩ = fun l { l }

include lib.list

val rec len_lemma : ∀a, ∀p:τ, ∀l∈slist⟨a,p⟩, ∃q:ι, p ≡ length l | p ≡ q =
  fun l {
    case l {
      []     → {}
      hd::tl → use len_lemma tl;
               let x = length tl;
               {}
    }
  }

val rec app : ∀a:ο, ∀n1 n2:ι, slist⟨a,n1⟩ ⇒ slist⟨a,n2⟩ ⇒ slist⟨a, n1 + n2⟩ =
  fun l1 l2 {
    case l1 {
      []     → l2
      hd::tl → let r = app tl l2;
               use len_lemma r; // necessary because if tl : slist⟨p⟩,
                   // we need to know that p+n2 is a value.
                   // and getting p by such that and let x = p + n2 is illegal
               hd::r
    }
  }


type rec typ = [ A; F of typ × typ ]

type rec term⟨c:τ→ο,a:τ⟩ =
  [ Var of c⟨a⟩
  ; App of ∃a' b:ι, term⟨c,F[(b,a')]⟩ × term⟨c,b⟩ | a ≡ a'
  ; Lam of ∃b d:ι, (c⟨b⟩ ⇒ term⟨c,d⟩) | a ≡ F[(b,d)]
  ]
type closed⟨a⟩ = ∀c, term⟨c,a⟩

val var : ∀c, ∀a, c⟨a⟩ ⇒ term⟨c,a⟩ = fun v { Var[v] }

val lam : ∀c:τ→ο, ∀a b:ι, (c⟨a⟩ ⇒ term⟨c,b⟩) ⇒ term⟨c,F[(a,b)]⟩ =
   fun f {  Lam[f] }

val up : ∀o:κ, ∀c, ∀a:ι, term^o⟨c,a⟩ ⇒ term⟨c,a⟩ = fun t { t }

val app : ∀c:τ→ο, ∀a b:ι, term⟨c,F[(b,a)]⟩ ⇒ term⟨c,b⟩ ⇒ term⟨c,a⟩ =
  fun f u { let p = (f, u); App[p] } // App[(f,u)] not working ???

val idt : ∀c:τ→ο, ∀a:ι, term⟨c,F[(a,a)]⟩ =
   lam(fun x { var x })


//val idt : ∀a:ι, closed⟨F(a,a)⟩ = let x = idt {}; x // nt correct because of value restriction

// include lib.either

// type sterm⟨c,a⟩ = term⟨(b:τ ↦ either⟨c⟨b⟩, term⟨c,b⟩⟩),a⟩
// type ssterm⟨o,c,a⟩ = term^o⟨(b:τ ↦ either⟨c⟨b⟩, term⟨c,b⟩⟩),a⟩

// val rec sub : ∀o, ∀c, ∀a:τ, ssterm⟨o,c,a⟩  ⇒ term⟨c,a⟩ =
//   fun t {
//     let c,a such that _ : term⟨c,a⟩;
//     case t {
//       Var[v] →
//         case (v:either⟨c⟨a⟩, term⟨c,a⟩⟩) {
//           InL[v] → Var[v]
//           InR[t] → t
//       }
//       App[(f,u)] →
//         let o,b:τ such that f : ssterm⟨o,c,F[(b,a)]⟩;
//         app (sub (f: ssterm⟨o,c,F[(b,a)]⟩)) (sub (u:ssterm⟨o,c,b⟩))
//       Lam[f]     →
//         let o,a:τ,b:τ such that f : either⟨c⟨a⟩, term⟨c,a⟩⟩ ⇒ ssterm⟨o,c,b⟩;
//         let g : c⟨a⟩ ⇒ term⟨c,b⟩ = fun (v:c⟨a⟩) {sub (f InL[v])};
//         Lam[g]
//     }
//   }

// val rec whnf : ∀o:κ, ∀c, ∀a:τ, sterm⟨c,a⟩ ↝ sterm⟨c,a⟩ =
//    fun t {
//      let c, a such that t : sterm⟨c,a⟩;
//      case t {
//        Var[v]     → t
//        Lam[f]     → t
//        App[(f,u)] → let o,b:τ such that u:ssterm⟨o,c,b⟩;
//                     let u : sterm⟨c,b⟩ = up u;
//                     let f : sterm⟨c,F[(b,a)]⟩ = up f;
//                     let g : sterm⟨c,F[(b,a)]⟩ = whnf f;
//                     //set log "stu";
//                     //
//                     case g {
//                       Var[_] → app g u
//                       App[_] → app g u
//                       Lam[f] → let u : term⟨c,b⟩ = sub u;
//                                let f : either⟨c⟨b⟩, term⟨c,b⟩⟩ ⇒ sterm⟨c,a⟩ =
//                                  fun x { sub (f x) };
//                                let h : sterm⟨c,a⟩ = f (InR[u] : either⟨c⟨b⟩, term⟨c,b⟩⟩);
//                                {-whnf (f (InR[u'] : either⟨c⟨b⟩, term⟨c,b⟩⟩))-}
//                     }
//      }
//    }
