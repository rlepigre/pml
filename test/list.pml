def list<a:ο> : ο = μx [ Nil of {} ; Cns of { hd : a; tl : x } ]

val nil : ∀a:ο, list<a> = Nil[{}]
val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> = fun e l → Cns[{ hd = e; tl = l }]

val map : ∀a b:ο, (a ⇒ b) ⇒ list<a> ⇒ list<b> = fix fun map f l →
  case l of
  | Nil[u] → Nil[{}]
  | Cns[c] → let hd = f c.hd in
             let tl = map f c.tl in
             Cns[{ hd = hd; tl = tl }]

def total<f:ι,a:ο> : ο = ∀x:ι, x∈a ⇒ ∃v:ι, f x ≡ v

//val map_map : ∀a b c:ο, ∀f∈(a ⇒ b), ∀g∈(b ⇒ c), total<f,a> ⇒
//     ∀l∈list<a>, map g (map f l) ≡ map (fun x → g (f x)) l =
//  fun fn gn h → fix fun map_map ls →
//    case ls of
//    | Nil[u] → ✂
//    | Cns[c] →
//        let hd = c.hd in
//        let tl = c.tl in
//        let show : map gn (map fn) ≡ map (fun x → gn (fn x)) l =
//          map_map tl
//        in
//        ✂
//
  
