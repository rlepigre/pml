type order<a:ο> = ∃cmp:ι, {
  cmp : cmp ∈ (a ⇒ a ⇒ bool);
  tmp : ∀x y∈a, ∃v:ι, v ≡ cmp x y;
  tra : ∀x y z∈a, (cmp x y ≡ tru ⇒ cmp y z ≡ tru ⇒ cmp x y ≡ tru);
  tot : ∀x y∈a, or (cmp x y) (cmp y x) ≡ tru
}

type rec list<a:ο> = μx [ Nil of {}; Cns of { hd : a; tl : list } ]

val nil : ∀a:ο, list<a> = Nil[]

def tl : ι = fun l → case l of | Cns[c] → c.tl
def hd : ι = fun l → case l of | Cns[c] → c.hd

val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l → Cns[{ hd = e; tl = l }]

val sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, bool = fix fun sorted o l →
  case l of
  | Nil[] → tru
  | Cns[c1] →
    let hd = c1.hd in let tl = c1.tl in
    (case tl of
    | Nil[] → tru
    | Cns[c2] →
       let hd2 = c2.hd in
       land<(o.cmp) hd hd2, sorted o tl>)

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
       let lem = o.tmp hd hd2 in
       (case o.cmp hd hd2 of
       | Tru[] →
          let lem : o.cmp hd hd2 ≡ tru = {} in
          let lem : sorted o l ≡ sorted o tl = {} in
          {}
       | Fls[] →
          let lem : o.cmp hd hd2 ≡ fls = {} in
          let lem : sorted o l ≡ fls = {} in {}))


val rec insert : ∀a:ο, order<a> ⇒ a ⇒ list<a> ⇒ list<a> = fun o x l →
   case l of
   | Nil[] → cns x nil
   | Cns[c1] →
     let hd = c1.hd in let tl = c1.tl in
     (case o.cmp x hd of
     | Tru[] → cns x l
     | Fls[] → cns hd (insert o x tl))

val rec insert_total :  ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈list<a>, ∃v:ι, insert o x l ≡ v = fun o x l →
   case l of
   | Nil[] → {}
   | Cns[c1] →
     let hd = c1.hd in let tl = c1.tl in
     let lem = o.tmp x hd in
     (case o.cmp x hd of
     | Tru[] → {}
     | Fls[] →
        let lem = insert_total o x tl in
        {})

val rec isort : ∀a:ο, order<a> ⇒ list<a> ⇒ list<a> = fun o l →
   case l of
   | Nil[] → nil
   | Cns[c1] →
     let hd = c1.hd in let tl = c1.tl in
     insert o hd (isort o tl)

val rec isort_total :  ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, ∃v:ι, isort o l ≡ v = fun o l →
   case l of
   | Nil[] → {}
   | Cns[c1] →
     let hd = c1.hd in let tl = c1.tl in
     let lem = isort_total o tl in
     let lem = insert_total o hd (isort o tl) in
     {}

type slist<a:ο,ord:τ> = ∃l:ι, l∈(list<a> | sorted ord l ≡ tru)

val rec tail_sorted :  ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈list<a>, sorted o (cns x l) ≡ tru ⇒ sorted o l ≡ tru = fun o x l hyp →
  case l of Nil[] → {}
          | Cns[c1] →
            let hd = c1.hd in
            let lem : (∃v:ι, o.cmp x hd ≡ v) = o.tmp x hd in
            let lem : (∃v:ι, sorted o l ≡ v) = sorted_total o l in
            (case o.cmp x hd of Tru[] →  {} | Fls[] → ✂)


val rec insert_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈slist<a,o>, sorted o (insert o x l) ≡ tru = Λa:ο.fun o x l →
   let cmp = o.cmp in
   case l of
   | Nil[] → {}
   | Cns[c1] →
     let hd = c1.hd in let tl = c1.tl in
     let lem = insert_total o x tl in
     let lem = o.tmp x hd in
     (case cmp x hd of
     | Tru[] →
         let lem : sorted o tl ≡ tru = tail_sorted o hd tl ({}:sorted o (cns hd tl) ≡ tru)  in
         {}
     | Fls[] →
         let lem : (∃v:ι, v ≡ cmp x hd) = o.tmp x hd in
         let lem : (∃v:ι, v ≡ cmp hd x) = o.tmp hd x in
         let lem : cmp hd x ≡ tru = o.tot x hd in
         (case tl of
             | Nil[] → {}
             | Cns[c2] →
                let hd2 = c2.hd in let tl2 = c2.tl in
                let lem = insert_total o x tl2 in
                let lem : (∃v:ι, v ≡ cmp hd hd2) = o.tmp hd hd2 in
                let lem : (∃v:ι, v ≡ cmp x hd2) = o.tmp x hd2 in
                (case cmp hd hd2 of Fls[] → ✂ | Tru[] →
                  let lem : sorted o (insert o x tl) ≡ tru = insert_sorted o x (tl:slist<a,o>) in
                  (case cmp x hd2 of
                  | Fls[] →
                     let lem : (∃v:ι, v ≡ cmp hd2 x) = o.tmp hd2 x in
                     let lem : (cmp hd2 x) ≡ tru = o.tot x hd2 in
                     {}
                  | Tru[] → {}
                  ))))

val rec isort_sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, sorted o (isort o l) ≡ tru = Λa:ο.fun o l →
   let cmp = o.cmp in
   case l of
   | Nil[] → {}
   | Cns[c1] →
      let hd = c1.hd in let tl = c1.tl in
      let lem = isort_total o tl in
      let lem = sorted_total o (isort o tl) in
      let ind : sorted o (isort o tl) ≡ true = isort_sorted o tl in
      let lem : (∃v:ι, insert o hd (isort o tl) ≡ v) = insert_total o hd (isort o tl) in
      let tls : slist<a,o> = isort o tl in
      let lem : sorted o (insert o hd (isort o tl)) ≡ tru = insert_sorted o hd tls in
      {}
