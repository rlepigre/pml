
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
  [ App of ∃a' b:ι, term⟨c,F[(b,a')]⟩ × term⟨c,b⟩ | a ≡ a'
  ; Lam of ∃b d:ι, (c⟨b⟩ ⇒ term⟨c,d⟩) | a ≡ F[(b,d)]
  ; Var of c⟨a⟩
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


include lib.either

type sterm⟨c,a⟩ = term⟨(b:τ ↦ either⟨c⟨b⟩, term⟨c,b⟩⟩),a⟩
type ssterm⟨o,c,a⟩ = term^o⟨(b:τ ↦ either⟨c⟨b⟩, term⟨c,b⟩⟩),a⟩

val rec sub : ∀c, ∀a:ι, sterm⟨c,a⟩  ⇒ term⟨c,a⟩ =
  fun t {
    case t {
      Var[v] →
        case v {
          InL[v] → var v
          InR[t] → t
      }
      App[(f,u)] → app (sub f) (sub u)
      Lam[f]     → lam (fun v {sub (f InL[v])})
    }
  }

val rec whnf_aux : ∀c, ∀a:ι, sterm⟨c,a⟩ →_(l) sterm⟨c,a⟩ =
  fun t {
      let c, a such that t : sterm⟨c,a⟩;
      case t {
        Var[v]     → t
        Lam[f]     → t
        App[(f,u)] → let f = whnf_aux f;
                     case f {
                       Var[_] → app f u
                       App[_] → app f u
                       Lam[f] → let u = sub u;
                                whnf_aux (f InR[u])
                      }
      }
  }

val whnf : ∀a:ι, closed⟨a⟩ →_(l) closed⟨a⟩ =
  fun t { sub (whnf_aux t) }
