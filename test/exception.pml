include lib.list

type bot = ∀x, x
type neg<a> = a ⇒ bot

val rec exists : ∀a:ο, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun f l {
    case l {
      Nil[_]  → false
      Cons[c] → f c.hd?true:exists f c.tl
    }
  }

def total<f:ι, a:ο> : ο = ∀x∈a, ∃y:ι, f x ≡ y

val rec exists_total : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>,
                         ∃v:ι, exists f l ≡ v =
  fun f ftot l {
    case l {
      Nil[_]  → {}
      Cons[c] →
        let lem : (∃y:ι, f c.hd ≡ y) = ftot c.hd;
        if f c.hd { {} }
        else { let lem = exists_total f ftot c.tl; {} }
    }
  }


val rec find : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒
                       ∀l∈list<a>, neg<(exists f l ≡ false)> ⇒ a =
  fun f ftot l exc {
    case l {
      | Nil[_]  → exc {}
      | Cons[c] → let hd = c.hd; let tl = c.tl;
                  let lem : (∃v:ι, f hd ≡ v) = ftot hd;
//                let exc : neg<exists f tl ≡ false> = exc in //useless !!!
                  f hd ? hd : find f ftot tl exc
    }
  }

val find_opt : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ list<a> ⇒ option<a> =
  fun f ftot l {
    save a {
      Some[find f ftot l (fun _ { restore a none })]
    }
  }

val notNone : ∀a:ο, option<a> ⇒ bool =
  fun o { case o { None → false | Some[_] → true } }

val rec find2 : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ list<list<a>> ⇒ option<a> =
  fun f ftot ls {
    case ls {
      Nil     → none
      Cons[c] →
        save a {
          Some[find f ftot c.hd (fun _ { restore a (find2 f ftot c.tl) })]
        }
    }
  }


//val find_opt2 : ∀a:ο, ∀f∈(a ⇒ bool), total<f,a> ⇒ ∀l∈list<a>,
//                ∃o:ι, option<a> | imp (exists f l) (notNone o) ≡ tru =
//  fun f ftot l { save a { Some[find f ftot l (fun _ { restore a none })] } }
