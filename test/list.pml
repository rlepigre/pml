def list<a:ο> : ο = μx [ Nil of {} ∈ {}; Cns of { hd : a; tl : x } ]

val nil : ∀a:ο, list<a> = Nil[]
val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l → Cns[{ hd = e; tl = l }]

val app : ∀a:ο, list<a> ⇒ list<a> ⇒ list<a> = fix fun app l1 l2 → case l1 of
  | Nil[] → nil
  | Cns[c] →  cns c.hd (app c.tl l2)

//val app_total : ∀a:ο, ∀l1 l2 ∈list<a>, ∃v:ι, app l1 l2 ≡ v =
//  fix fun app_total l1 l2 →
//    case l1 of
//    | Nil[] → {}
//    | Cns[c] → let ind = app_total c.tl l2 in {}
//
//val app_asso : ∀a:ο, ∀l1 l2 l3∈list<a>, app l1 (app l2 l3) ≡ app (app l1 l2) l3 =
//  fix fun app_asso l1 l2 l3 →
//    case l1 of
//    | Nil[] → {}
//    | Cns[c] →
//       let total = app_total l2 l3 in
//       let ind = app_asso c.tl l2 l3 in
//       {}
//
val map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> = fix fun map f l →
  case l of
  | Nil[u] → Nil[{}]
  | Cns[c] → let hd = f c.hd in
             let tl = map f c.tl in
             Cns[{ hd = hd; tl = tl }]

def total<f:ι,a:ο> : ο = ∀x∈a, ∃v:ι, f x ≡ v

//val map_total : ∀a b:ο, ∀f∈(a ⇒ b), total<f,a> ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
//  fix fun map_total fn ft ls →
//  case ls of
//  | Nil[] → {}
//  | Cns[c] →
//        let hd = c.hd in
//        let tl = c.tl in
//        let lem : (∃v:ι, fn hd ≡ v) = ft hd in
//        let ind : (∃v:ι, map fn tl ≡ v) = map_total fn ft tl in
//        {}
//

//val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
//     ∀l∈list<a>, map g (map f l) ≡ map (fun x → g (f x)) l =
//  fix fun map_map fn gn tf tg ls →
//    case ls of
//    | Nil[] → {}
//    | Cns[c] →
//        let hd = c.hd in
//        let tl = c.tl in
//        let lem = tf hd in
//        let lem = tg (fn hd) in
//        let show : map gn (map fn tl) ≡ map (fun x → gn (fn x)) tl =
//          map_map fn gn tf tg tl
//        in
//        {}
