include lib.option

type fifo_sig_aux<fifo:ο→ο> =
  { empty : ∀a, fifo<a>
  ; push  : ∀a, a ⇒ fifo<a> ⇒ fifo<a>
  ; pop   : ∀a, fifo<a> ⇒ option<a * fifo<a>> }

type fifo_sig = ∃fifo:ο→ο, fifo_sig_aux<fifo>

include lib.list

val fifo_simple : fifo_sig =
   { empty = nil
   ; push  = fun e s { e::s }
   ; pop   = fun s { case rev s { [] → None | e :: s → Some[(e,rev s)] } }
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

type ope<a> = [ Push of a ; Pop ]

// apply a sequence of operations and performs a last "pop"
// FIXME: Unexpected exception [Raw.Too_many_args(_)].
// val apply : ∀a, fifo_sig ⇒ ope<a> ⇒ option<a> =
//   fun fifo ops {
//     let t such that fifo : fifo_sig_aux<t>;
//     let rec fn : ∀a, t<a> ⇒ ope<a> ⇒ t<a> =
//       fun f ops {
//         case ops {
//           []      → f
//           op::ops → case op {
//             Push[x] → fifo.push x f
//             Pop     → case fifo.pop f {
//               None → f
//               Some[(e,f)] → f
//             }
//           }
//         }
//       };
//     let f = fn fifo.empty ops;
//     case pop f {
//       None → None
//       Some[(e,f)] → Some[e]
//     }
//   }