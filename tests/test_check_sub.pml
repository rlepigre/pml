type a = [ A ]

val x : {} = {}

assert a ⊂ a

type nat = μ x, [Z ; S of x]

assert nat ⊂ nat

type nat2 = μ x, [Z ; S of [ Z ; S of x]]

assert nat2 ⊂ nat
assert nat ⊂ nat2

include lib.nat
include lib.list

type vec⟨a:ο,s:τ⟩ = ∃l:ι, l∈(list⟨a⟩ | length l ≡ s)

type rec slist⟨a,s:τ⟩ =
  [ Nil of ({} | s ≡ Zero)
  ; Cons of { hd : a; tl : ∃p:τ, slist⟨a,p⟩ | S[p] ≡ s}]

val rec sub1 : ∀a,∀s, vec⟨a,s⟩ ⊂ slist⟨a,s⟩ =
  fun l { case l {
                 | [] → []
                 | x::l' → x::sub1 l'}}

val id1a : ∀a,∀s, vec⟨a,s⟩ ⇒ slist⟨a,s⟩ = fun l { check sub1 l for l }

val id1b : ∀a,∀s, vec⟨a,s⟩ ⇒ slist⟨a,s⟩ =
  check sub1 : ∀a,∀s, vec⟨a,s⟩ ⊂ slist⟨a,s⟩; fun x {x}


// Le sous typage automatique ne marche pas. C'est bizarre
// car la preuve de sous-typage doit beaucoup ressembler
// à la preuve de typage de sub1.
assert ? ∀s:τ,∀a:ο, vec⟨a,s⟩ ⊂ slist⟨a,s⟩


val rec sub2 : ∀a,∀s, slist⟨a,s⟩ ⊂ vec⟨a,s⟩ =
  fun l {
    let s,a such that l : slist⟨a,s⟩;
    case l {
    | []    → []
    | x::l' → let s',o such that l' : slist^o⟨a,s'⟩;
              let  l'' : l' ∈ vec⟨a,s'⟩ = sub2 (l': slist^o⟨a,s'⟩);
              x::l''}}

val id2a : ∀a,∀s, slist⟨a,s⟩ ⇒ vec⟨a,s⟩ = fun l { check sub2 l for l}

val id2b : ∀a,∀s, slist⟨a,s⟩ ⇒ vec⟨a,s⟩  =
  check sub2 : ∀a,∀s, slist⟨a,s⟩ ⊂ vec⟨a,s⟩; fun l {l}

//ça marche encore moins.
//val x : {} = set log "s"; check ∀s:τ,∀a:ο,∀l:ι, l∈nlist⟨a,s⟩ ⊂ l∈(list⟨a⟩ | length l ≡ s); {}
