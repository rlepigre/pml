type a = [ A ]

val x : {} = {}

val x : {} = check (a) ⊂ (a) ; {}

type nat = μ x, [Z ; S of x]

val x : {} = check nat ⊂ nat ; {}

type nat2 = μ x, [Z ; S of [ Z ; S of x]]

val x : {} = check nat2 ⊂ nat ; {}
val x : {} = check nat ⊂ nat2 ; {}

include lib.nat
include lib.list

type vec⟨a:ο,s:τ⟩ = ∃l:ι, l∈(list⟨a⟩ | length l ≡ s)

type rec slist⟨a,s:τ⟩ =
  [ Nil of ({} | s ≡ Zero)
  ; Cons of { hd : a; tl : ∃p:τ, slist⟨a,p⟩ | S[p] ≡ s}]

val rec sub1 : ∀a,∀s,∀l ∈ vec⟨a,s⟩, l ∈ slist⟨a,s⟩ =
  fun l { case l {
                 | [] → []
                 | x::l' → x::sub1 l'}}

val id1 : ∀a,∀s,∀l ∈ vec⟨a,s⟩, l ∈ slist⟨a,s⟩ =
  fun l { check sub1 l for l }

// Le sous typage automatique ne marche pas. C'est bizarre
// car la preuve de sous-typage doit beaucoup ressembler
// à la preuve de typage de sub1.
//val x : {} = check ∀s:τ,∀a:ο, vec⟨a,s⟩ ⊂ slist⟨a,s⟩; {}


val rec sub2 : ∀a,∀s,∀l ∈ slist⟨a,s⟩, l ∈ vec⟨a,s⟩ =
  fun l {
    let s,a such that l : slist⟨a,s⟩;
    case l {
    | []    → []
    | x::l' → let s',o such that l' : slist^o⟨a,s'⟩;
              let  l'' : l' ∈ vec⟨a,s'⟩ = sub2 (l': slist^o⟨a,s'⟩);
              x::l''}}

val id2 : ∀a,∀s,∀l ∈ slist⟨a,s⟩, l ∈ vec⟨a,s⟩ =
  fun l { check sub2 l for l}

//ça marche encore moins.
//val x : {} = set log "s"; check ∀s:τ,∀a:ο,∀l:ι, l∈nlist⟨a,s⟩ ⊂ l∈(list⟨a⟩ | length l ≡ s); {}
