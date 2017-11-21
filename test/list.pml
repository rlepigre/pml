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

val rec app_total : ∀a:ο, ∀l1 l2 ∈list<a>, ∃v:ι, app l1 l2 ≡ v =
  fun l1 l2 {
    case l1 {
      Nil[_] → {}
      Cns[c] → let ind = app_total c.tl l2; {}
    }
  }

val rec app2_total : ∀a:ο, ∀l1 l2 ∈list<a>, ∃v:ι, app2 l1 l2 ≡ v =
  fun l1 l2 {
    case l1 {
      Nil[_] → {}
      Cns[c] → let ind = app2_total c.tl l2; {}
    }
  }

val rec app_asso : ∀a:ο, ∀x1 x2 x3∈list<a>, app x1 (app x2 x3) ≡ app (app x1 x2) x3 =
  fun l1 l2 l3 {
    case l1 {
      Nil    →
       let total = app_total l2 l3; {}
      Cns[c] →
       let hd = c.hd;
       let tl = c.tl;
       let total = app_total tl l2;
       let total = app_total l2 l3;
       let total = app_total tl (app l2 l3); // FIXME: worked without why ?
       let total = app_total (app tl l2) l3; // FIXME: worked without why ?
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
       let total = app2_total l2 l3; {}
      Cns[c] →
       let hd = c.hd;
       let tl = c.tl;
       let total = app2_total tl l2;
       let total = app2_total l2 l3;
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

def total<f:ι,a:ο> : ο = ∀x∈a, ∃v:ι, f x ≡ v

val compose_total : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
                    total<f,a> ⇒ total<g,b> ⇒ total<(fun x { g (f x) }), a> =
  fun fn gn tf tg a {
    let lem = tf a;
    let lem = tg (fn a); {}
  }

val rec map_total : ∀a b:ο, ∀f∈(a ⇒ b), total<f,a>
                    ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
  fun fn ft ls {
    case ls {
      Nil    → {}
      Cns[c] →
        let hd = c.hd;
        let tl = c.tl;
        let lem : (∃v:ι, fn hd ≡ v) = ft hd;
        let ind : (∃v:ι, map fn tl ≡ v) = map_total fn ft tl; {}
    }
  }

val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b>
              ⇒ ∀l∈list<a>, map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun fn gn {
    fix map_map { fun tf tg ls {
      case ls {
        Nil    → {}
        Cns[c] →
          let hd = c.hd; let tl = c.tl;
          let tgf = compose_total fn gn tf tg hd;
          let lem = tf hd;
          let lem = map_total fn tf tl;
          let ind = map_map tf tg tl; {}
      }
    }
  }}

val rec map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
    ∀l∈list<a>, map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun fn gn tf tg ls {
    case ls {
      Nil    → {}
      Cns[c] →
        let hd = c.hd;
        let tl = c.tl;
        let gof = fun x { gn (fn x) };
        let tgf = compose_total fn gn tf tg;
        let lem : (∃v:ι, map gof tl ≡ v) = map_total gof tgf tl;
        let lem = tf hd;
        let lem = tg (fn hd);
        let lem = tgf hd;
        let lem = map_total fn tf tl;
        let lem = map_total gn tg (map fn tl);
        let lem = map_total gof tgf tl;
        let ind : map gn (map fn tl) ≡ map gof tl = map_map fn gn tf tg tl;
        let ded : gn (fn hd) ≡ gof hd = {};
        let ded : map gn (map fn ls) =
          Cns[{ hd = gn (fn hd) ; tl = map gn (map fn tl)}] = {};
        let ded : map gof ls =
          Cns[{ hd = gof hd ; tl = map gof tl }] = {}; {}
    }
  }
