type rec list<a:ο> = [ Nil of {}; Cns of { hd : a; tl : list } ]

val nil : ∀a:ο, list<a> = Nil

def tl : ι = fun l { case l { Cns[c] → c.tl } }
def hd : ι = fun l { case l { Cns[c] → c.hd } }

val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l { Cns[{ hd = e; tl = l }] }

val rec app : ∀b:ο, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      Nil[_] → nil
      Cns[c] → let hd = c.hd in
               let tl = app c.tl l2 in
               Cns[{ hd = hd; tl = tl }]
    }
  }

val rec app2 : ∀b:ο, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      Nil    → nil
      Cns[c] → cns c.hd (app2 c.tl l2)
    }
  }

def app0 : ι =
  fix fun app l1 l2 {
    case l1 {
      Nil    → l2
      Cns[c] → let r = app c.tl l2 in cns c.hd r
    }
  }

val appt : ∀b:ο, list<b> ⇒ list<b> ⇒ ∃w:ι, (w∈list<b>) = app0

val rec app_total : ∀a:ο, ∀l1 l2 ∈list<a>, ∃v:ι, app l1 l2 ≡ v =
  fun l1 l2 {
    case l1 {
      Nil[_] → {}
      Cns[c] → let ind = app_total c.tl l2 in {}
    }
  }

val rec app_asso : ∀a:ο, ∀x1 x2 x3∈list<a>, app x1 (app x2 x3) ≡ app (app x1 x2) x3 =
  fun l1 l2 l3 {
    case l1 {
      Nil    →
       let total = app_total l2 l3 in
       {}
      Cns[c] →
       let hd = c.hd in
       let tl = c.tl in
       let total = app_total tl l2 in
       let total = app_total l2 l3 in
       let ded : app l1 (app l2 l3) ≡ cns hd (app tl (app l2 l3)) = {} in
       let ded : app (app l1 l2) l3 ≡ cns hd (app (app tl l2) l3) = {} in
       let ind : app tl (app l2 l3) ≡ app (app tl l2) l3 =
         app_asso tl l2 l3
       in {}
    }
  }

val rec map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> =
  fun f l {
    case l {
      Nil    → Nil
      Cns[c] → let hd = f c.hd in
               let tl = map f c.tl in
               Cns[{hd= hd; tl= tl}]
    }
  }

def total<f:ι,a:ο> : ο = ∀x∈a, ∃v:ι, f x ≡ v

val compose_total : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
                    total<f,a> ⇒ total<g,b> ⇒ total<(fun x { g (f x) }), a> =
  fun fn gn tf tg a {
    let lem = tf a in
    let lem = tg (fn a) in {}
  }

val rec map_total : ∀a b:ο, ∀f∈(a ⇒ b), total<f,a>
                    ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
  fun fn ft ls {
    case ls {
      Nil    → {}
      Cns[c] →
        let hd = c.hd in
        let tl = c.tl in
        let lem : (∃v:ι, fn hd ≡ v) = ft hd in
        let ind : (∃v:ι, map fn tl ≡ v) = map_total fn ft tl in {}
    }
  }

val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b>
              ⇒ ∀l∈list<a>, map g (map f l) ≡ map (fun x { g (f x) }) l =
  fun fn gn {
    fix fun map_map tf tg ls {
      case ls {
        Nil    → {}
        Cns[c] →
          let hd = c.hd in let tl = c.tl in
          let tgf = compose_total fn gn tf tg hd in
          let lem = tf hd in
          let lem = map_total fn tf tl in
          let ind = map_map tf tg tl in {}
      }
    }
  }

val comp : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), a ⇒ c = fun f g x { g (f x) }

// FIXME : replacing comp by its definition fails, pb for equality under
//         lambda

val rec map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
    ∀l∈list<a>, map g (map f l) ≡ map (comp f g) l =
  fun fn gn tf tg ls {
    case ls {
      Nil    → {}
      Cns[c] →
        let hd = c.hd in
        let tl = c.tl in
        let gof = fun x { gn (fn x) } in
        let tgf = compose_total fn gn tf tg in
        let lem : (∃v:ι, map gof tl ≡ v) = map_total gof tgf tl in
        let lem = tf hd in
        let lem = tg (fn hd) in
        let lem = tgf hd in
        let lem = map_total fn tf tl in
        let lem = map_total gn tg (map fn tl) in
        let lem = map_total gof tgf tl in
        let ind : map gn (map fn tl) ≡ map gof tl = map_map fn gn tf tg tl in
        let ded : gn (fn hd) ≡ gof hd = {} in
        let ded : map gn (map fn ls) =
          Cns[{ hd = gn (fn hd) ; tl = map gn (map fn tl)}] = {}
        in
        let ded : map gof ls =
          Cns[{ hd = gof hd ; tl = map gof tl }] = {}
        in {}
    }
  }
