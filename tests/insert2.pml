include lib.bool
include lib.list

type order⟨a:ο⟩ = ∃cmp:ι,
  { cmp : cmp ∈ (a ⇒ a ⇒ bool)
//  ; tra : ∀x y z∈a, (cmp x y ⇒ cmp y z ⇒ cmp x y)
  ; tot : ∀x y∈a, or (cmp x y) (cmp y x) }

val orev : ∀a, order⟨a⟩ ⇒ order⟨a⟩ =
  fun o { {
      cmp = fun x y { o.cmp y x },
      tot = fun x y { o.tot y x }}}

val rec sorted : ∀a:ο, ∀o∈order⟨a⟩, ∀l∈list⟨a⟩, bool =
  fun o l {
    case l {
      []     → true
      hd::tl →
        case tl {
          []       → true
          hd2::tl2 → o.cmp hd hd2 && sorted o tl
       }
    }
  }

val rec tail_sorted : ∀a:ο, ∀o∈order⟨a⟩, ∀x∈a, ∀l∈list⟨a⟩,
          sorted o (x::l) ⇒ sorted o l =
  fun o x l _ { set auto 2 2; qed }

type slist⟨s,a:ο,ord:τ⟩ = ∃l:ι, l∈(list^s⟨a⟩ | sorted ord l)

val head : ∀a, list⟨a⟩ ⇒ a ⇒ a =
  fun l default { case l { [] → default | x::_ → x }}

val tail : ∀a,∀o∈order⟨a⟩, slist⟨∞,a,o⟩ ⇒ slist⟨∞,a,o⟩ =
    fun o l { set auto 2 1; case l { [] → [] | _::l → l}}

val before : ∀a,∀o∈order⟨a⟩, list⟨a⟩ ⇒ list⟨a⟩ ⇒ bool = fun o l1 l2 {
  case l1 {
    [] → true
    x::_ → case l2 { [] → true | y::_ → o.cmp x y } } }

val head_less : ∀a,∀o∈order⟨a⟩, a ⇒ list⟨a⟩ ⇒ bool =
    fun o x l { case l { [] → true | y::_ → o.cmp x y }}

val lem : ∀a,∀o∈order⟨a⟩, ∀x∈a, ∀l∈(slist⟨∞,a,o⟩|head_less o x l), sorted o (x::l) =
    fun o x l { set auto 1 0; qed }

val rec rev_append : ∀s,∀a,∀o∈order⟨a⟩, ∀l1∈slist⟨s,a,orev o⟩,
                       ∀l2∈slist⟨∞,a,o⟩|before o l1 l2, slist⟨∞,a,o⟩ =
    fun o l1 l2 { set auto 2 1;
      case l1 {
        [] → []
        x::l → rev_append o l (x::l2)
      }}

val rec insert : ∀s,∀a:ο, ∀o∈order⟨a⟩, a ⇒ slist⟨s,a,o⟩ ⇒ slist⟨s+ₒ1,a,o⟩ =
  fun o x l {
    let a such that x:a;
    // show that some lemma may be integrated in the function
    let cmp = fun x y {let _ = o.tot x y; o.cmp x y};
    set auto 4 6 1;
    case l {
      []     → x::[]
      hd::tl → if cmp x hd { x::l } else { hd :: insert o x tl }
    }
  }

val rec isort : ∀s,∀a:ο, ∀o∈order⟨a⟩, slist⟨s,a,o⟩ ⇒ slist⟨s,a,o⟩ =
  fun o l {
    set auto 2 1;
    case l {
      []     → []
      hd::tl → insert o hd (isort o tl)
    }
  }
