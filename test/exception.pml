include lib.list
include test.mu

val rec exists : ∀a:ο, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun f l →
    case l of
    | Nil[_]  → false
    | Cons[c] → if f c.hd then true else exists f c.tl

def total<f:ι, a:ο> : ο = ∀x∈a, ∃y:ι, f x ≡ y

val rec exists_total : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>,
                         ∃v:ι, exists f l ≡ v =
  fun f ftot l →
    case l of
    | Nil[_]  → {}
    | Cons[c] →
        let lem : (∃y:ι, f c.hd ≡ y) = ftot c.hd in
        if f c.hd then {} else (let lem = exists_total f ftot c.tl in {})


val rec find : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>, neg<(exists f l ≡ false)> ⇒ a =
  fun f ftot l exc →
    case l of
    | Nil[_]  → exc {}
    | Cons[c] → let hd = c.hd in let tl = c.tl in
                let lem : (∃v:ι, f hd ≡ v) = ftot hd in
//                 let exc : neg<exists f tl ≡ false> = exc in //useless !!!
                if f hd then hd else find f ftot tl exc

val find_opt : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ list<a> ⇒ option<a> =
  fun f ftot l → save a → Some[find f ftot l (fun _ → restore a none)]

val notNone : ∀a:ο, option<a> ⇒ bool = fun o →
  case o of None[] → fls | Some[_] → tru

val rec find2 : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ list<list<a>> ⇒ option<a> =
  fun f ftot ls →
    case ls of Nil[_]  → none
             | Cons[c] → let l = c.hd in let tl = c.tl in
                         save a → Some[find f ftot l (fun _ → restore a (find2 f ftot tl))]


//val find_opt2 : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>, ∃o:ι, option<a> |
//      imp (exists f l) (notNone o) ≡ tru  =
//  fun f ftot l → save a → Some[find f ftot l (fun _ → restore a none)]
