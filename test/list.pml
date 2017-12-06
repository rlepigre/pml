type rec list<a:ο> = [ Nil of {}; Cns of { hd : a; tl : list } ]

val nil : ∀a:ο, list<a> = Nil

def tl : ι = fun l { case l { Cns[c] → c.tl } }
def hd : ι = fun l { case l { Cns[c] → c.hd } }

val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l { Cns[{ hd = e; tl = l }] }

val rec app : ∀b:ο, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      Nil[_] → l2
      Cns[c] → let hd = c.hd;
               let tl = app c.tl l2;
               Cns[{ hd = hd; tl = tl }]
    }
  }

val rec app2 : ∀b:ο, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      Nil    → l2
      Cns[c] → cns c.hd (app2 c.tl l2)
    }
  }

def app0 : τ =
  fix app { fun l1 l2 {
    case l1 {
      Nil    → l2
      Cns[c] → let r = app c.tl l2; cns c.hd r
    }
  }}

val appt : ∀b:ο, list<b> ⇒ list<b> ⇒ ∃w:ι, (w∈list<b>) = app0

val rec app_asso : ∀a:ο, ∀x1 x2 x3∈list<a>, app x1 (app x2 x3) ≡ app (app x1 x2) x3 =
  fun l1 l2 l3 {
    case l1 {
      Nil    →
       {}
      Cns[c] →
       let hd = c.hd;
       let tl = c.tl;
       let ded : app l1 (app l2 l3) ≡ cns hd (app tl (app l2 l3)) = {};
       let ded : app (app l1 l2) l3 ≡ cns hd (app (app tl l2) l3) = {};
       let ind : app tl (app l2 l3) ≡ app (app tl l2) l3 =
         app_asso tl l2 l3; {}
    }
  }

val rec app2_asso : ∀a:ο, ∀x1 x2 x3∈list<a>, app2 x1 (app2 x2 x3) ≡ app2 (app2 x1 x2) x3 =
  fun l1 l2 l3 {
    case l1 {
      Nil    →
       {}
      Cns[c] →
       let hd = c.hd;
       let tl = c.tl;
       let ded : app2 l1 (app2 l2 l3) ≡ cns hd (app2 tl (app2 l2 l3)) = {};
       let ded : app2 (app2 l1 l2) l3 ≡ cns hd (app2 (app2 tl l2) l3) = {};
       let ind : app2 tl (app2 l2 l3) ≡ app2 (app2 tl l2) l3 =
         app2_asso tl l2 l3; {}
    }
  }

val rec map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> =
  fun f l {
    case l {
      Nil    → Nil
      Cns[c] → let hd = f c.hd;
               let tl = map f c.tl;
               Cns[{hd= hd; tl= tl}]
    }
  }

val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), ∀l∈list<a>,
                        map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun fn gn {
    fix map_map { fun ls {
      case ls {
        Nil    → {}
        Cns[c] →
          let hd = c.hd; let tl = c.tl;
          let tgf = gn (fn hd);
          let lem = fn hd;
          let lem = map fn tl;
          let ind = map_map tl; {}
      }
    }
  }}

val rec map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), ∀l∈list<a>,
                            map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun fn gn ls {
    case ls {
      Nil    → {}
      Cns[c] →
        let hd = c.hd;
        let tl = c.tl;
        let gof = fun x { gn (fn x) };
        let lem = fn hd;
        let lem = gn (fn hd);
        let lem = map fn tl;
        let ind : map gn (map fn tl) ≡ map gof tl = map_map fn gn tl;
        let ded : gn (fn hd) ≡ gof hd = {};
        let ded : map gn (map fn ls) ==
          Cns[{ hd = gn (fn hd) ; tl = map gn (map fn tl)}] = {};
        let ded : map gof ls ==
          Cns[{ hd = gof hd ; tl = map gof tl }] = {}; {}
    }
  }
