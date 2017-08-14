// Proofs on lists

include lib.list

val rec app_total : ∀a, ∀l1 l2 ∈list<a>, ∃v:ι, app l1 l2 ≡ v =
  fun l1 l2 {
    case l1 {
      Nil     → {}
      Cons[c] → use { app_total c.tl l2 }
    }
  }

val rec app_asso : ∀a, ∀x y z∈list<a>, app x (app y z) ≡ app (app x y) z =
  fun l1 l2 l3 {
    case l1 {
      | Nil     →
         let total = app_total l2 l3 in
         {}
      | Cons[c] →
         let hd = c.hd in
         let tl = c.tl in
         let total = app_total tl l2 in
         let total = app_total l2 l3 in
         let ded : app l1 (app l2 l3) ≡ cons hd (app tl (app l2 l3)) = {} in
         let ded : app (app l1 l2) l3 ≡ cons hd (app (app tl l2) l3) = {} in
         let ind : app tl (app l2 l3) ≡ app (app tl l2) l3 = app_asso tl l2 l3
         in {}
    }
  }

def total<f:ι,a> = ∀x∈a, ∃v:ι, f x ≡ v
def cmp<f:ι,g:ι> = fun x { g (f x) }

val compose_total : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c),
                    total<f,a> ⇒ total<g,b> ⇒ total<cmp<f,g>, a> =
  fun f g tf tg a { use { tf a}; use { tg (f a) } }

val rec map_total : ∀a b, ∀f∈(a⇒b), total<f,a>
                    ⇒ ∀l∈list<a>, ∃v:ι, map f l ≡ v =
  fun fn ft ls {
    case ls {
      | Nil     → {}
      | Cons[c] →
         let hd = c.hd in
         let tl = c.tl in
         let lem : (∃v:ι, fn hd ≡ v) = ft hd in
         let ind : (∃v:ι, map fn tl ≡ v) = map_total fn ft tl in {}
    }
  }

val map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
    ∀l∈list<a>, map g (map f l) ≡ map cmp<f,g> l =
  fun fn gn {
    fix fun map_map tf tg ls {
      case ls {
        | Nil     → {}
        | Cons[c] →
           let hd = c.hd in let tl = c.tl in
           let tgf = compose_total fn gn tf tg hd in
           let lem = tf hd in
           let lem = map_total fn tf tl in
           let ind = map_map tf tg tl in {}
      }
    }
  }

val comp : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), a ⇒ c = fun f g x { g (f x) }

// FIXME : replacing comp by its definition fails, pb for equality under
//         lambda

val rec map_map : ∀a b c, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒ total<g,b> ⇒
    ∀l∈list<a>, map g (map f l) ≡ map (comp f g) l =
  fun fn gn tf tg ls {
    case ls {
    | Nil     → {}
    | Cons[c] →
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
        {}
    }
  }

val rec length_total : ∀a:ο, ∀l∈list<a>, ∃v:ι, v ≡ length l =
  fun l {
    case l {
      Nil[_]  → {}
      Cons[c] → let ind = length_total c.tl in {}
    }
  }

