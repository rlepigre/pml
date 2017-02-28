def cons<a:ο,b:ο> = ∃v w:ι, { hd = v; tl = w } ∈ { hd : a; tl : b }

def list<a:ο> : ο = μx [ Nil of {} ∈ {}; Cns of cons<a,x> ]

val nil : ∀a:ο, list<a> = Nil[]

def tl : ι = fun l → case l of | Cns[c] → c.tl
def hd : ι = fun l → case l of | Cns[c] → c.hd

val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l → Cns[{ hd = e; tl = l }]

val app : ∀b:ο, list<b> ⇒ list<b> ⇒ list<b> = fix fun app l1 l2 → case l1 of
  | Nil[]  → nil
  | Cns[c] →
     let hd = c.hd in
     let tl = app c.tl l2 in
     Cns[{ hd = hd; tl = tl }]

val app2 : ∀b:ο, list<b> ⇒ list<b> ⇒ list<b> = fix fun app l1 l2 → case l1 of
  | Nil[]  → nil
  | Cns[c] →
     cns c.hd (app c.tl l2)

def app0 : ι = fix fun app l1 l2 → case l1 of
  | Nil[]  → nil
  | Cns[c] →
     cns c.hd (app c.tl l2)

val appt : ∀b:ο, list<b> ⇒ list<b> ⇒ ∃w:ι, (w∈list<b>) = app0

val app_total : ∀a:ο, ∀l1 l2 ∈list<a>, ∃v:ι, app l1 l2 ≡ v =
  fix fun app_total l1 l2 →
    case l1 of
    | Nil[] → {}
    | Cns[c] →
      let hd = c.hd in
      let tl = c.tl in
      let ind = app_total tl l2 in {}

val app_asso : ∀a:ο, ∀x1 x2 x3∈list<a>, app x1 (app x2 x3) ≡ app (app x1 x2) x3 =
  fix fun app_asso l1 l2 l3 →
    case l1 of
    | Nil[] →
       let total = app_total l2 l3 in
       {}
    | Cns[c] →
       let hd = c.hd in
       let tl = c.tl in
       let total = app_total tl l2 in
       let total = app_total l2 l3 in
       let deduce : app l1 (app l2 l3) ≡ cns hd (app tl (app l2 l3))  = {} in
       let deduce : app (app l1 l2) l3 ≡ cns hd (app (app tl l2) l3)  = {} in
       let ind : app tl (app l2 l3) ≡ app (app tl l2) l3 = app_asso tl l2 l3 in
       {}

val map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> = fix fun map f l →
  case l of
  | Nil[] → Nil[]
  | Cns[c] → let hd = f c.hd in
             let tl = map f c.tl in
             cns hd tl

def total<f:ι,a:ο> : ο = ∀x∈a, ∃v:ι, f x ≡ v

val compose_total : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
                            total<f,a> ⇒ total<g,b> ⇒ total<(fun x → g (f x)), a> =
  fun fn gn tf tg a → let lem = tf a in
                      let lem = tg (fn a) in {}

val map_total : ∀a b:ο, ∀f∈(a ⇒ b), total<f,a> ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
  fix fun map_total fn ft ls →
  case ls of
  | Nil[] → {}
  | Cns[c] →
        let hd = c.hd in
        let tl = c.tl in
        let lem : (∃v:ι, fn hd ≡ v) = ft hd in
        let ind : (∃v:ι, map fn tl ≡ v) = map_total fn ft tl in
        let deduce : map fn ls ≡ cns (fn hd) (map fn tl) = {} in
        {}

val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
     ∀l∈list<a>, map g (map f l) ≡ map (fun x → g (f x)) l =
  fix fun map_map fn gn tf tg ls →
    case ls of
    | Nil[] → {}
    | Cns[c] →
        let hd = c.hd in
        let tl = c.tl in
        let lem = tf hd in
        let lem = tg (fn hd) in
        let lem = map_total fn tf tl in
        let lem = map_total gn tg (map fn tl) in
        let deduce : map gn (map fn ls) ≡ cns (gn (fn hd)) (map gn (map fn tl)) = {} in
        let tgf = compose_total fn gn tf tg in
        let lem = map_total (fun x → gn (fn x)) tgf tl in
        let deduce : map (fun x → gn (fn x)) ls
                   ≡ cns (gn (fn hd)) (map (fun x → gn (fn x)) tl) = {}
        in
        let show : map gn (map fn tl) ≡ map (fun x → gn (fn x)) tl =
          map_map fn gn tf tg tl
        in
        {}