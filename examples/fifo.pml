include lib.option

// fifo signature with a parametric type as parameter for the
// internal representation.
type fifo_sig_open⟨fifo:ο→ο⟩ =
  { empty : ∀a, fifo⟨a⟩
  ; push  : ∀a, a ⇒ fifo⟨a⟩ ⇒ fifo⟨a⟩
  ; pop   : ∀a, fifo⟨a⟩ ⇒ option⟨a × fifo⟨a⟩⟩ }

// fifo signature with the type abstracted by an existential.
type fifo_sig = ∃fifo:ο→ο, fifo_sig_open⟨fifo⟩

include lib.list
include lib.list_proofs

// fifo as list
val take_last : ∀a, list⟨a⟩ ⇒ option⟨a × list⟨a⟩⟩ =
  fun s { case rev s { [] → None | e :: s → Some[(e,rev s)] } }

// one value with two types (open and abstracted*)
val fifo_simple_open : fifo_sig_open⟨list⟩ =
   { empty = nil
   ; push  = fun e s { e::s }
   ; pop   = take_last
   }

val fifo_simple : fifo_sig = fifo_simple_open

// fifo as pair of lists
type list2⟨a⟩ = list⟨a⟩ × list⟨a⟩

val rec pop : ∀a, list2⟨a⟩ ⇒ option⟨a × list2⟨a⟩⟩ =
  fun p {
    case p.2 {
      x::s2 → Some[(x,(p.1,s2))]
      []    → case p.1 {
        []    → None
        x::s0 → pop ([], rev p.1)
      }
    }
  }

val push :  ∀a, a ⇒ list2⟨a⟩ ⇒ list2⟨a⟩ =
  fun e p { let (s1,s2) = p; ((e::s1), s2) }

// one value with two types (open and abstracted*)
val fifo_pair_open : fifo_sig_open⟨list2⟩ =
   { empty = ((nil, nil) : ∀a, list2⟨a⟩)
   ; push  = push
   ; pop   = pop }

val fifo_pair : fifo_sig = fifo_pair_open

// now we prove the equivalence of the two implementation

// translation as an untyped macro
def translate⟨f:τ⟩ = app f.1 (rev f.2)

// lemma for the empty fifo (computation only)
val equiv_empty : translate⟨fifo_pair.empty⟩ ≡ fifo_simple.empty = {}

// lemma for push
val equiv_push :
  ∀a, ∀x∈a, ∀f∈list2⟨a⟩,
    translate⟨fifo_pair.push x f⟩ ≡ fifo_simple.push x translate⟨f⟩ =
  fun x f {
    let (s1,s2) = f;
    deduce fifo_pair.push x f ≡ ((x::s1), s2);
    deduce translate⟨((x::s1), s2)⟩ ≡ app (x::s1) (rev s2);
    deduce translate⟨f⟩ ≡ app s1 (rev s2);
    let _ = rev s2;
    {}
  }

// lemma for po, the crucial case (needs a definition,
// and a few intermediate lemmas)
def translate_opt⟨o:τ⟩ =
  case o { None → None | Some[(x,f)] → Some[(x,translate⟨f⟩)] }

val rec lemma1 : ∀a, ∀x∈a, ∀s1∈list⟨a⟩, ∀s2∈list⟨a⟩,
    take_last (app s1 (rev (x::s2))) ≡ Some[(x,app s1 (rev s2))] =
  fun x s1 s2 {
    let a such that s2 : list⟨a⟩;
    let s2':list⟨a⟩ = Cons[{hd=x; tl=s2}];
    let _ = rev s2';
    let _ = rev s1;
    let _ = app s1 (rev s2');
    let _ = rev (app s1 (rev s2')); // why necessary ?
    deduce take_last (app s1 (rev s2')) ≡
      case rev (app s1 (rev s2')) { [] → None | e :: s → Some[(e,rev s)] };
    show rev (app s1 (rev s2')) ≡ rev_app (rev s2') (rev s1)
      using app_rev_rev1 (rev s2') s1 [];
    let _ = app s2' (rev s1);
    show rev (app s1 (rev s2')) ≡ app s2' (rev s1)
      using app_rev_rev2 s2' [] (rev s1);
    deduce rev (app s1 (rev s2')) ≡ x::(app s2 (rev s1));
    let _ = app s2 (rev s1);
    deduce take_last (app s1 (rev s2')) ≡
      Some[(x,rev (app s2 (rev s1)))] ;
    show rev (app s2 (rev s1)) ≡ rev_app (rev s1) (rev s2)
      using app_rev_rev1 (rev s1) s2 [];
    let _ = rev s2;
    show rev (app s2 (rev s1)) ≡ rev_app [] (app s1 (rev s2))
      using app_rev_rev2 s1 [] (rev s2);
    let _ = app s1 (rev s2);
    deduce rev (app s2 (rev s1)) ≡ app s1 (rev s2);
    {}
  }

val rec lemma2 : ∀a, ∀s1∈list⟨a⟩,
                  app s1 [] ≡ app [] (rev (rev s1))
  = fun s1 { use app_nil s1; use rev_rev s1 }

val rec equiv_pop :
  ∀a, ∀f∈list2⟨a⟩,
      translate_opt⟨fifo_pair.pop f⟩ ≡ fifo_simple.pop translate⟨f⟩ =
  fun f {
    let a such that f : list2⟨a⟩;
    let (s1,s2) = f;
    case s2 {
      x::s2' →
        deduce fifo_pair.pop f ≡ Some[(x,(s1,s2'))];
        deduce translate⟨f⟩ ≡ app s1 (rev (x::s2'));
        deduce translate_opt⟨fifo_pair.pop f⟩ ≡ Some[(x,app s1 (rev s2'))];
        deduce fifo_simple.pop translate⟨f⟩
          ≡ take_last (app s1 (rev (x::s2')));
        use lemma1 x s1 s2'
      [] →
        case s1 {
          []      → {}
          x1::s1' →
            let _ = rev s1;
            deduce fifo_pair.pop f ≡ fifo_pair.pop ([], rev s1);
            deduce translate⟨f⟩ ≡ app s1 [];
            deduce translate⟨([], rev s1)⟩ ≡ app [] (rev (rev s1));
            show translate⟨f⟩ ≡ translate⟨([], rev s1)⟩
              using lemma2 s1;
            use equiv_pop ([], rev s1)
        }
    }
  }

// to define equivalence, we define the type of operation on fifo
// and the application of a list of operations.
type ope⟨a⟩ = [ Push of a ; Pop ]

val rec apply_aux : ∀t,∀a, fifo_sig_open⟨t⟩ ⇒ t⟨a⟩ ⇒ list⟨ope⟨a⟩⟩ ⇒ t⟨a⟩ =
  fun fifo f ops {
    let t such that fifo:fifo_sig_open⟨t⟩;
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

// apply a sequence of operations and performs a last "pop"
val apply : ∀a, fifo_sig ⇒ list⟨ope⟨a⟩⟩ ⇒ option⟨a⟩ =
  fun fifo ops {
    let a such that _ : option⟨a⟩;
    let t such that fifo : fifo_sig_open⟨t⟩;
    let fifo:fifo_sig_open⟨t⟩ = fifo;
    let f : t⟨a⟩ = apply_aux fifo fifo.empty ops;
    case fifo.pop f {
      None        → None
      Some[(e,f)] → Some[e]
    }
  }

//which gives the following type for equivalence of fifo implementations
def equiv_fifo⟨fifo1,fifo2⟩ =
  ∀a, ∀ops∈list⟨ope⟨a⟩⟩, apply fifo1 ops ≡ apply fifo2 ops

// and we prove the main theorem from a lemma
val rec equiv_apply_aux :
  ∀a, ∀f∈list2⟨a⟩, ∀ops∈list⟨ope⟨a⟩⟩,
    translate⟨apply_aux fifo_pair f ops⟩ ≡
      apply_aux fifo_simple translate⟨f⟩ ops =
  fun f ops {
    let fifo_pair = fifo_pair_open;
    let a such that f : list2⟨a⟩;
    let (l1, l2) = f;
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
                show translate⟨apply_aux fifo_pair f1 ops'⟩ ≡
                  apply_aux fifo_simple translate⟨f1⟩ ops'
                  by equiv_apply_aux f1 ops';
                {}
            }
          Push[x] →
            use equiv_push x f;
            let f1:list⟨a⟩×list⟨a⟩ = ((x::l1), l2);
            show translate⟨apply_aux fifo_pair f1 ops'⟩
              ≡ apply_aux fifo_simple translate⟨f1⟩ ops'
              by equiv_apply_aux f1 ops';
            {}
        }
    }
  }

val rec th : equiv_fifo⟨fifo_pair,fifo_simple⟩ =
  fun ops {
    let a such that ops:list⟨ope⟨a⟩⟩;
    let fifo_pair = fifo_pair_open;
    let fifo_simple = fifo_simple_open;
    // need the type annotation of .empty because otherwise, a
    // constant parametric type is inferred for the type of fifo in
    // apply_aux
    let f1 = apply_aux fifo_pair (fifo_pair.empty:list2⟨a⟩) ops;
    let f2 = apply_aux fifo_simple (fifo_simple.empty:list⟨a⟩) ops;
    show translate⟨f1⟩ ≡ f2 by equiv_apply_aux fifo_pair.empty ops;
    show translate_opt⟨fifo_pair.pop f1⟩ ≡ fifo_simple.pop f2 by
      equiv_pop f1;
    case fifo_pair.pop f1 {
      None        → {}
      Some[(e,f)] → {}
    }
  }
