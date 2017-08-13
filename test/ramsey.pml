include lib.nat
include lib.stream

type sum<a,b> = [ Inl of a; Inr of b ]

type pro<a,b> = { fst : a; snd : b }

type col_t<f,a> = ∃v, v∈a | f v ≡ true
type col_f<f,a> = ∃v, v∈a | f v ≡ false

type sstream<o,a> = νo stream {} ⇒ {hd : a; tl : stream}

type stream_t<o,f,a> = sstream<o,col_t<f,a>>
type stream_f<o,f,a> = sstream<o,col_f<f,a>>

def to_term<s:σ> = fun x → restore s x

def total<f, a> : ο = ∀x∈a, ∃y:ι, f x ≡ y

// val rec aux : ∀o1 o2, ∀a, ∀f∈(a⇒bool), total<f,a> ⇒ (stream_t<o1,f,a> ⇒ ∀x,x) ⇒ (stream_f<o2,f,a> ⇒ ∀x,x) ⇒ stream<a> ⇒ ∀x,x
//             = fun f ft ct cf s →
//               let c = s {} in
//               use ft c.hd;
//               case f c.hd {
//               | true  → deduce f c.hd ≡ true;
//                         ct (fun _ → { hd = c.hd; tl = save ct → aux f ft to_term<ct> cf c.tl } )
//               | false → deduce f c.hd ≡ false;
//                         cf (fun _ → { hd = c.hd; tl = save cf → aux f ft ct to_term<cf> c.tl } )
//               }

// val infinite_tape
//   : ∀a, ∀f∈(a ⇒ bool), total<f,a> ⇒ stream<a> ⇒ sum<stream_t<f,a>,stream_f<f,a>>
//   = fun f ft s →
//     save a → Inl[save ct → restore a
//              Inr[save cf →
//                aux f ft to_term<ct> to_term<cf> s ]]
