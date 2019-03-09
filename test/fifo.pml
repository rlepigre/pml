include lib.option

type fifo_sig_aux⟨fifo:ο→ο⟩ =
  { empty : ∀a, fifo⟨a⟩
  ; push  : ∀a, a ⇒ fifo⟨a⟩ ⇒ fifo⟨a⟩
  ; pop   : ∀a, fifo⟨a⟩ ⇒ option⟨a × fifo⟨a⟩⟩ }

type fifo_sig = ∃fifo:ο→ο, fifo_sig_aux⟨fifo⟩

include lib.list
include lib.list_proofs

val take_last : ∀a, list⟨a⟩ ⇒ option⟨a × list⟨a⟩⟩ =
  fun s { case rev s { [] → None | e :: s → Some[(e,rev s)] } }

val fifo_simple : fifo_sig =
   { empty = nil
   ; push  = fun e s { e::s }
   ; pop   = take_last
   }

type slist⟨a,s⟩ = μ_s list, [ Nil ; Cons of { hd : a; tl : list}  ]

val rec pop : ∀a, list⟨a⟩ × list⟨a⟩ ⇒ option⟨a × (list⟨a⟩ × list⟨a⟩)⟩ =
  fun p {
    case p.2 {
      x::s2 → Some[(x,(p.1,s2))]
      []    → case p.1 {
        []    → None
        x::s0 → pop ([], rev p.1)
      }
    }
  }

val push :  ∀a, a ⇒ list⟨a⟩ × list⟨a⟩ ⇒ list⟨a⟩ × list⟨a⟩ =
  fun e p { let (s1,s2) = p; ((e::s1), s2) }

type pl⟨a⟩ = list⟨a⟩ × list⟨a⟩

val fifo_pair : fifo_sig =
   { empty = ((nil, nil) : ∀a, list⟨a⟩ × list⟨a⟩)
   ; push  = push
   ; pop   = pop }

def translate⟨f:τ⟩ = app f.1 (rev f.2)

val equiv_empty : translate⟨fifo_pair.empty⟩ ≡ fifo_simple.empty = {}

val equiv_push :
  ∀a, ∀x∈a, ∀f∈list⟨a⟩ × list⟨a⟩,
    translate⟨fifo_pair.push x f⟩ ≡ fifo_simple.push x translate⟨f⟩ =
  fun x f {
    let (s1,s2) = f;
    deduce fifo_pair.push x f ≡ ((x::s1), s2);
    deduce translate⟨((x::s1), s2)⟩ ≡ app (x::s1) (rev s2);
    deduce translate⟨f⟩ ≡ app s1 (rev s2);
    use rev s2;
    {}
  }

def translate_opt⟨o:τ⟩ =
  case o { None → None | Some[(x,f)] → Some[(x,translate⟨f⟩)] }

val rec lemma1 : ∀a, ∀x∈a, ∀s1∈list⟨a⟩, ∀s2∈list⟨a⟩,
                   take_last (app s1 (rev (x::s2))) ≡ Some[(x,app s1 (rev s2))] =
  fun x s1 s2 {
    let a such that s2 : list⟨a⟩;
    let s2':list⟨a⟩ = Cons[{hd=x; tl=s2}];
    use rev s2';
    use rev s1;
    use app s1 (rev s2');
    use rev (app s1 (rev s2')); // why necessary ?
    deduce take_last (app s1 (rev s2')) ≡
      case rev (app s1 (rev s2')) { [] → None | e :: s → Some[(e,rev s)] };
    show rev (app s1 (rev s2')) ≡ rev_app (rev s2') (rev s1)
      using app_rev_rev1 (rev s2') s1 [];
    use app s2' (rev s1);
    show rev (app s1 (rev s2')) ≡ app s2' (rev s1)
      using app_rev_rev2 s2' [] (rev s1);
    deduce rev (app s1 (rev s2')) ≡ x::(app s2 (rev s1));
    use app s2 (rev s1);
    deduce take_last (app s1 (rev s2')) ≡
      Some[(x,rev (app s2 (rev s1)))] ;
    show rev (app s2 (rev s1)) ≡ rev_app (rev s1) (rev s2)
      using app_rev_rev1 (rev s1) s2 [];
    use rev s2;
    show rev (app s2 (rev s1)) ≡ rev_app [] (app s1 (rev s2))
      using app_rev_rev2 s1 [] (rev s2);
    use app s1 (rev s2);
    deduce rev (app s2 (rev s1)) ≡ app s1 (rev s2);
    {}
  }

val rec lemma2 : ∀a, ∀s1∈list⟨a⟩,
                  app s1 [] ≡ app [] (rev (rev s1))
  = fun s1 { use app_nil s1; use rev_rev s1 }

val rec equiv_pop :
  ∀a, ∀f∈list⟨a⟩ × list⟨a⟩,
      translate_opt⟨fifo_pair.pop f⟩ ≡ fifo_simple.pop translate⟨f⟩ =
  fun f {
    let a such that f : (list⟨a⟩ × list⟨a⟩);
    let (s1,s2) = f;
    case s2 {
      x::s2' →
        deduce fifo_pair.pop f ≡ Some[(x,(s1,s2'))];
        deduce translate⟨f⟩ ≡ app s1 (rev (x::s2'));
        deduce translate_opt⟨fifo_pair.pop f⟩ ≡ Some[(x,app s1 (rev s2'))];
        deduce fifo_simple.pop translate⟨f⟩ ≡ take_last (app s1 (rev (x::s2')));
        use lemma1 x s1 s2'
      [] →
        case s1 {
          []      → {}
          x1::s1' →
            use rev s1;
            deduce fifo_pair.pop f ≡ fifo_pair.pop ([], rev s1);
            deduce translate⟨f⟩ ≡ app s1 [];
            deduce translate⟨([], rev s1)⟩ ≡ app [] (rev (rev s1));
            show translate⟨f⟩ ≡ translate⟨([], rev s1)⟩
              using lemma2 s1;
            use equiv_pop ([], rev s1)
        }
    }
  }

type ope⟨a⟩ = [ Push of a ; Pop ]

val rec apply_aux : ∀t,∀a, fifo_sig_aux⟨t⟩ ⇒ t⟨a⟩ ⇒ list⟨ope⟨a⟩⟩ ⇒ t⟨a⟩ =
  fun fifo f ops {
    let t such that fifo:fifo_sig_aux⟨t⟩;
    let a such that f:t⟨a⟩;
    case ops {
      []      → f
      op::ops →
        let f:t⟨a⟩ = case op {
          Push[x] → fifo.push x f
          Pop     → case fifo.pop f {
            None        → fifo.empty
            Some[(e,f)] → f
          }
        };
        apply_aux fifo (f:t⟨a⟩) ops
    }
  }

val rec equiv_apply_aux :
  ∀a, ∀f∈list⟨a⟩ × list⟨a⟩, ∀ops∈list⟨ope⟨a⟩⟩,
    translate⟨apply_aux fifo_pair f ops⟩ ≡
      apply_aux fifo_simple translate⟨f⟩ ops =
  fun f ops {
    let a such that f : list⟨a⟩ × list⟨a⟩;
    let (l1, l2) = f;
    eqns f ≡ (l1, l2);
    case ops {
      []      → {}
      op::ops' →
        case op {
          Pop     →
            use equiv_pop f;
            case fifo_pair.pop f {
              None →
                deduce apply_aux fifo_pair f ops ≡
                         apply_aux fifo_pair ([], []) ops';
                use equiv_apply_aux ([], []) ops';
                {}
              Some[(e,f1)] →
                deduce apply_aux fifo_pair f ops ≡
                         apply_aux fifo_pair f1 ops';
                eqns translate⟨apply_aux fifo_pair f1 ops'⟩ ≡
                  apply_aux fifo_simple translate⟨f1⟩ ops'
                  by equiv_apply_aux f1 ops';
                {}
            }
          Push[x] →
            use equiv_push x f;
            let f1:list⟨a⟩×list⟨a⟩ = ((x::l1), l2);
            eqns translate⟨apply_aux fifo_pair f1 ops'⟩
              ≡ apply_aux fifo_simple translate⟨f1⟩ ops' by equiv_apply_aux f1 ops';
            {}
        }
    }
  }

// apply a sequence of operations and performs a last "pop"
val apply : ∀a, fifo_sig ⇒ list⟨ope⟨a⟩⟩ ⇒ option⟨a⟩ =
  fun fifo ops {
    let a such that _ : option⟨a⟩;
    let t such that fifo : fifo_sig_aux⟨t⟩;
    let fifo:fifo_sig_aux⟨t⟩ = fifo;
    let f : t⟨a⟩ = apply_aux fifo fifo.empty ops;
    case fifo.pop f {
      None        → None
      Some[(e,f)] → Some[e]
    }
  }

def equiv_fifo⟨fifo1,fifo2⟩ =
  ∀a, ∀ops∈list⟨ope⟨a⟩⟩, apply fifo1 ops ≡ apply fifo2 ops

val rec th : equiv_fifo⟨fifo_pair,fifo_simple⟩ =
  fun ops {
    let a such that ops:list⟨ope⟨a⟩⟩;
    let fifo_pair : fifo_sig_aux⟨pl⟩ = fifo_pair;
    let fp : pl⟨a⟩ = fifo_pair.empty;
    let f1 = apply_aux fifo_pair fp ops; // FIXME: should work without the 2 previous lines
    let fifo_simple : fifo_sig_aux⟨list⟩ = fifo_simple;
    let fl : list⟨a⟩ = fifo_simple.empty;
    let f2 = apply_aux fifo_simple fl ops; // FIXME: should work without the 2 previous lines
    eqns translate⟨f1⟩ ≡ f2 by equiv_apply_aux fp ops;
    eqns translate_opt⟨fifo_pair.pop f1⟩ ≡ fifo_simple.pop f2 by
      equiv_pop f1;
    case fifo_pair.pop f1 {
      None        → {}
      Some[(e,f)] → {}
    }
  }
