include lib.nat
include lib.nat_proofs
include lib.list
include lib.list_proofs

// Type of vectors (list of a given length).
type vec<a,n> = ∃l, l∈(list<a> | length l ≡ n)

// Append function.
val rec app : ∀a, ∀m n:ι, vec<a,m> ⇒ vec<a,n> ⇒ vec<a, add m n> =
  fun l1 l2 {
    case l1 {
      Nil     → l2
      Cons[c] → let _  = length_total c.tl in
                let tl = app c.tl l2 in
                Cons[{hd = c.hd; tl = tl}]
    }
  }

// Ternary append function.
val app3 : ∀a, ∀m n p:ι, vec<a,m> ⇒ vec<a,n> ⇒ vec<a,p>
                       ⇒ vec<a, add m (add n p)> =
  fun l1 l2 l3 {
    use add_total (length l2) (length l3);
    app l1 (app l2 l3)
  }

// Transform a vector into a list (immediate with subtyping).
val vec_to_list : ∀a, ∀s, vec<a,s> ⇒ list<a> = fun x { x }

