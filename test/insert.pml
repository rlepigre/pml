include test.bool

type order<a:ο> = ∃cmp:ι, {
  cmp : cmp ∈ (a ⇒ a ⇒ bool);
  tmp : ∀x y∈a, ∃v:ι, v ≡ cmp x y;
  tra : ∀x y z∈a, (cmp x y ≡ tru ⇒ cmp y z ≡ tru ⇒ cmp x y ≡ tru);
  tot : ∀x y∈a, or (cmp x y) (cmp y x) ≡ tru
}

include test.list

val sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, bool = fix fun sorted o l →
  case l of
  | Nil[] → tru
  | Cns[c1] →
    let hd = c1.hd in let tl = c1.tl in
    (case tl of
    | Nil[] → tru
    | Cns[c2] →
       let hd2 = c2.hd in
       land<o.cmp hd hd2, sorted o tl>)

val sorted_total : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, ∃v:ι, v ≡ sorted o l =
  fix fun sorted_total o l →
  case l of
  | Nil[] → {}
  | Cns[c1] →
    let hd = c1.hd in let tl = c1.tl in
    (case tl of
    | Nil[] → {}
    | Cns[c2] →
       let hd2 = c2.hd in
       let tl2 = c2.tl in
       let ind : (∃v:ι, v ≡ sorted o tl) = sorted_total o tl in
       let lem : l ≡ cns hd (cns hd2 tl2) = {} in
       let lem : (λx.x) (sorted o tl) ≡ sorted o tl = {} in
       let lem = o.tmp hd hd2 in
       (case o.cmp hd hd2 of
       | T[] →
          let lem : o.cmp hd hd2 ≡ tru = {} in
          let lem : sorted o l ≡ sorted o tl = {} in
          let ind : (∃v:ι, v ≡ sorted o tl) = sorted_total o tl in //???
          {}
       | F[] →
          let lem : o.cmp hd hd2 ≡ fls = {} in
          let lem : sorted o l ≡ fls = {} in {}))

type slist<a:ο,ord:τ> = ∃l:ι, l∈(list<a> | sorted ord l ≡ tru)

//val insert : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈slist<a,o>, slist<a,o> = fix fun insert o x l →
//  let ded : sorted o l ≡ tru = {} in
//  case l of
//  | Nil[] → Nil[]
//  | Cns[c1] →
//    let hd = c1.hd in let tl = c1.tl in
//    let lem = o.tmp x hd in
//    (case o.cmp x hd of
//    | T[] →
//        cns x l
//    | F[] →
//        let ded : o.cmp x hd ≡ fls = {} in
//        let lem = o.tmp x hd in
//        let lem = o.tmp hd x in
//        let lem : o.cmp hd x ≡ tru = o.tot x hd in
//        (case tl of
//           | Nil[] → {}
//           | Cns[c2] →
//              let hd2 = c2.hd in
//              let tl2 = c2.tl in
//              let lem : l ≡ cns hd (cns hd2 tl2) = {} in
//              let lem = o.tmp hd hd2 in
//              let lem = sorted_total o l in
//              let lem = sorted_total o tl in
//              let ded : sorted o l ≡ land<o.cmp hd hd2, sorted o tl> = {} in //???
//              (case (o.cmp hd hd2) of
//                       | F[] → ✂
//                       | T[] →
//        //let ded : sorted o tl ≡ tru = {} in
//        //let res = cns hd (insert o x tl) in
//        ✂)))
