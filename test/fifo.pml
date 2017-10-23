include lib.option

type fifo_sig_aux<fifo:ο→ο> =
  { empty : ∀a, fifo<a>
  ; push  : ∀a, a ⇒ fifo<a> ⇒ fifo<a>
  ; pop   : ∀a, fifo<a> ⇒ option<a * fifo<a>> }

type fifo_sig = ∃fifo:ο→ο, fifo_sig_aux<fifo>

include lib.list
include lib.list_proofs

val take_last : ∀a, list<a> ⇒ option<a*list<a>> =
  fun s { case rev s { [] → None | e :: s → Some[(e,rev s)] } }

val fifo_simple : fifo_sig =
   { empty = nil
   ; push  = fun e s { e::s }
   ; pop   = take_last
   }

type slist<a,s> = μ_s list, [ Nil ; Cons of { hd : a; tl : list}  ]

// FIXME: termination fails if we use a pair of lists. It should not!
val rec pop : ∀a, list<a> ⇒ list<a> ⇒ option<a * (list<a> * list<a>)> =
  fun s1 s2 {
    case s2 {
      x::s2 → Some[(x,(s1,s2))]
      []    → case s1 {
        []    → None
        x::s0 →
          pop [] (rev s1)
      }
    }
  }

val fifo_pair : fifo_sig =
   { empty = ((nil, nil) : ∀a, list<a> * list<a>)
   ; push  = fun e p { let (s1,s2) = p; ((e::s1), s2) }
   ; pop   = fun p { pop p.1 p.2 } }

def translate<f:τ> = app f.1 (rev f.2)

val equiv_empty : translate<fifo_pair.empty> ≡ fifo_simple.empty = {}

val equiv_push :
  ∀a, ∀x∈a, ∀f∈list<a>*list<a>,
    translate<fifo_pair.push x f> ≡ fifo_simple.push x translate<f> =
  fun x f {
    let (s1,s2) = f;
    deduce fifo_pair.push x f ≡ ((x::s1), s2);
    deduce translate<((x::s1), s2)> ≡ app (x::s1) (rev s2);
    deduce translate<f> ≡ app s1 (rev s2);
    use rev_total s2;
    {}
  }

def translate_opt<o:τ> =
  case o { None → None | Some[(x,f)] → Some[(x,translate<f>)] }

val rec lemma1 : ∀a, ∀x∈a, ∀s1∈list<a>, ∀s2∈list<a>,
                   take_last (app s1 (rev (x::s2))) ≡ Some[(x,app s1 (rev s2))] =
  fun x s1 s2 {
    let a such that s2 : list<a>;
    let s2':list<a> = Cons[{hd=x; tl=s2}];
    use rev_total s2';
    use rev_total s1;
    use app_total s1 (rev s2');
    use rev_total (app s1 (rev s2')); // why necessary ?
    deduce take_last (app s1 (rev s2')) ≡
      case rev (app s1 (rev s2')) { [] → None | e :: s → Some[(e,rev s)] };
    show rev (app s1 (rev s2')) ≡ rev_app (rev s2') (rev s1)
      using app_rev_rev1 (rev s2') s1 [];
    use app_total s2' (rev s1);
    show rev (app s1 (rev s2')) ≡ app s2' (rev s1)
      using app_rev_rev2 s2' [] (rev s1);
    deduce rev (app s1 (rev s2')) ≡ x::(app s2 (rev s1));
    use app_total s2 (rev s1);
    deduce take_last (app s1 (rev s2')) ≡
      Some[(x,rev (app s2 (rev s1)))] ;
    show rev (app s2 (rev s1)) ≡ rev_app (rev s1) (rev s2)
      using app_rev_rev1 (rev s1) s2 [];
    use rev_total s2;
    show rev (app s2 (rev s1)) ≡ rev_app [] (app s1 (rev s2))
      using app_rev_rev2 s1 [] (rev s2);
    use app_total s1 (rev s2);
    deduce rev (app s2 (rev s1)) ≡ app s1 (rev s2);
    {}
  }

val rec lemma2 : ∀a, ∀s1∈list<a>,
                  app s1 [] ≡ app [] (rev (rev s1))
  = fun s1 { use app_nil s1; use rev_rev s1 }

val rec equiv_pop :
  ∀a, ∀f∈list<a>*list<a>,
      translate_opt<fifo_pair.pop f> ≡ fifo_simple.pop translate<f> =
  fun f {
    let a such that f : (list<a>*list<a>);
    let (s1,s2) = f;
    case s2 {
      x::s2' →
        deduce fifo_pair.pop f ≡ Some[(x,(s1,s2'))];
        deduce translate<f> ≡ app s1 (rev (x::s2'));
        deduce translate_opt<fifo_pair.pop f> ≡ Some[(x,app s1 (rev s2'))];
        deduce fifo_simple.pop translate<f> ≡ take_last (app s1 (rev (x::s2')));
        // FIXME: why typing annotation on x ?
        use lemma1 (x:a) s1 s2'
      [] →
        case s1 {
          []      → {}
          x1::s1' →
            use rev_total s1;
            deduce fifo_pair.pop f ≡ fifo_pair.pop ([], rev s1);
            deduce translate<f> ≡ app s1 [];
            deduce translate<([], rev s1)> ≡ app [] (rev (rev s1));
            show translate<f> ≡ translate<([], rev s1)>
              using lemma2 s1;
            use equiv_pop ([], rev s1)
        }
    }
  }


type ope<a> = [ Push of a ; Pop ]

val rec apply_aux : ∀t,∀a, fifo_sig_aux<t> ⇒ t<a> ⇒ list<ope<a>> ⇒ t<a> =
  fun fifo f ops {
    let t such that fifo:fifo_sig_aux<t>;
    let a such that f:t<a>;
    case ops {
      []      → f
      op::ops →
        let f:t<a> = apply_aux fifo f ops;
        case op {
          Push[x] → fifo.push x f
          Pop     → case fifo.pop f {
            None        → f
            Some[(e,f)] → f
          }
        }
    }
  }

val rec apply_aux_total : ∀t,∀a, ∀fifo∈fifo_sig_aux<t>, ∀f∈t<a>, ∀ops∈list<ope<a>>,
                            ∃v:ι, apply_aux fifo f ops ≡ v =
  fun fifo f ops { {-requires to know that push and pop are total-} }

// apply a sequence of operations and performs a last "pop"
val apply : ∀a, fifo_sig ⇒ list<ope<a>> ⇒ option<a> =
  fun fifo ops {
    let a such that _ : option<a>;
    let t such that fifo : fifo_sig_aux<t>;
    let fifo:fifo_sig_aux<t> = fifo;
    let f : t<a> = apply_aux fifo fifo.empty ops;
    case fifo.pop f {
      None        → None
      Some[(e,f)] → Some[e]
    }
  }

def equiv_fifo<fifo1,fifo2> =
  ∀a, ∀ops∈list<ope<a>>, apply fifo1 ops ≡ apply fifo2 ops

// val rec fifo_pair_aux :
//   ∀a, ∀ops∈list<ope<a>>,
//      ∃l1 l2∈list<a>, apply_aux fifo_pair fifo_pair.empty ops ≡ (l1,l2) =
//   fun ops {
//     let a such that ops : list<ope<a>>;
//     let fp = fifo_pair;
//     let t such that fp : fifo_sig_aux<t>;
//     let fp : fifo_sig_aux<t> = fp;
//     case ops {
//       []      → (nil,nil, {})
//       op::ops' →
//         let (l1,l2,u) = fifo_pair_aux ops';
//         let f : t<a> = apply_aux fp fp.empty ops';
//         deduce f ≡ (l1,l2);
//         case op {
//           Pop     →
//             use apply_aux_total fp fp.empty ops';
//             deduce apply_aux fp fp.empty ops ≡

// (        let f:t<a> = apply_aux fp fp.empty ops';
//         case op {
//           Push[x] → fp.push x f
//           Pop     → case fp.pop f {
//             None        → f
//             Some[(e,f)] → f
//           }
//         });

//            //   case fp.pop f { None → f | Some[(e,f)] → f };
//             case fp.pop f {
//               None        → deduce apply_aux fp fp.empty ops ≡ f;
//                             (l1,l2,{})
//               Some[(e,p)] → (p.1,p.2,{})
//             }
//           Push[x] → (x::l1,l2,{})
//         }
//     }
//   }

val rec th : equiv_fifo<fifo_pair,fifo_simple> =
  fun ops {
    case ops {
      []      → {}
      op::ops → {--}
    }
  }