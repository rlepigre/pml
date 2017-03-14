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


//val rec find : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>, neg<(exists f l ≡ false)> ⇒ a =
//  Λa:ο. fun f ftot l exc →
//    case l of
//    | Nil[_]  → ✂
//    | Cons[c] → let hd = c.hd in
//                let tl = c.tl in
//                let lem : (∃v:ι, f hd ≡ v) = ftot hd in
//                if f hd then hd else
//                  (let lem2 = exists_total f ftot tl in
//                   let deduce : exists f l ≡ exists f tl = {} in
//                   let exc' : neg<(((exists f) tl) ≡ false)> = exc in
//                   find f ftot tl exc')


//val find : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>, neg<(exists f l ≡ false)> ⇒ a =
//  fun f ftot → fix fun find l exc →
//    case l of
//    | Nil[_]  → ✂
//    | Cons[c] → let hd = c.hd in
//                let tl = c.tl in
//                let lem : (∃v:ι, f hd ≡ v) = ftot hd in
//                if f hd then hd else
//                  (let lem2 = exists_total f ftot tl in
//                   let deduce : exists f l ≡ exists f tl = {} in
//                   let deduce : f hd ≡ false = {} in
//                   let exc' : neg<(((exists f) tl) ≡ false)> = exc in
//                   find tl exc')
