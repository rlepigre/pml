include lib.either
include lib.nat
include lib.stream

type pro<a,b> = { fst : a; snd : b }

type col_t<f,a> = ∃v, v∈a | f v ≡ true
type col_f<f,a> = ∃v, v∈a | f v ≡ false

type sstream<o,a> = νo stream {} ⇒ {hd : a; tl : stream}

type stream_t<o,f,a> = sstream<o,col_t<f,a>>
type stream_f<o,f,a> = sstream<o,col_f<f,a>>

type cstream<o,a> = {hd : a; tl : sstream<o,a>}
type cstream_t<o,f,a> = {hd : col_t<f,a>; tl : stream_t<o,f,a>}
type cstream_f<o,f,a> = {hd : col_f<f,a>; tl : stream_f<o,f,a>}


def total<f, a> : ο = ∀x∈a, ∃y:ι, f x ≡ y

val abort : ∀y, (∀x,x) ⇒ y = fun x → x

def to_term<s:σ> = fun x → abort (restore s x)

val rec aux : ∀o1 o2, ∀a, ∀f∈(a⇒bool), total<f,a>
             ⇒ (cstream_t<o1,f,a> ⇒ ∀x,x)
             ⇒ (cstream_f<o2,f,a> ⇒ ∀x,x)
             ⇒ stream<a> ⇒ ∀x,x =
  fun f ft ct cf s {
    let c = s {} in
    let hd = c.hd in
    let tl = c.tl in
    use ft hd;
    if f hd {
      ct { hd = hd; tl = fun _ → save ct → abort (aux f ft to_term<ct> cf c.tl)}
    } else {
      cf { hd = hd; tl = fun _ → save cf → abort (aux f ft ct to_term<cf> c.tl)}
    }
  }

val infinite_tape : ∀a, ∀f∈(a ⇒ bool), total<f,a> ⇒ stream<a>
                    ⇒ either<stream_t<∞,f,a>,stream_f<∞,f,a>> =
  fun f ft s {
    save a {
      InL[fun _ { save ct { restore a InR[fun _ { save cf {
        abort (aux f ft to_term<ct> to_term<cf> s) }}]}}]
    }
  }

type bstream<o,a> = νo stream {} ⇒ either<{hd:a; tl:stream}, {hd:a; tl:stream}>
type cbstream<o,a> = either<{hd:a; tl:bstream<o,a>}, {hd:a; tl:bstream<o,a>}>

type color<a> = a ⇒ stream<a> ⇒ either<stream<a>,stream<a>>

val rec aux2 : ∀o1 o2, ∀a, ∀f∈color<a>,
                (cstream<o1,a> ⇒ ∀x,x)
             ⇒ (cstream<o2,a> ⇒ ∀x,x)
             ⇒ stream<a> ⇒ ∀x,x =
  fun f ct cf s {
    let c = s {} in
    let hd = c.hd in
    let tl = c.tl in
    case f hd tl {
      InL[s] →
        ct { hd = hd; tl = fun _ {
            save ct { abort (aux2 f to_term<ct> cf s) } } }
      InR[s] →
        cf { hd = hd; tl = fun _ {
            save cf { abort (aux2 f ct to_term<cf> s) } } }
      }
  }

val infinite_tape2 : ∀a, ∀f∈color<a>, stream<a>
                    ⇒ either<stream<a>,stream<a>> =
  fun f s {
    save a {
      InL[fun _ { save ct { restore a InR[fun _ { save cf {
        abort (aux2 f to_term<ct> to_term<cf> s) }}]}}]
    }
  }

val ramsey2 : ∀a, ∀f∈(a ⇒ a ⇒ bool), stream<a>
  ⇒ either<stream<a>,stream<a>> =
  fun f s {
    let a such that f : a ⇒ a ⇒ bool in
    let color1 : color<a> = fun a1 s {
      let color2 : color<a> = fun a2 s {
          if f a1 a2 then inl s else inr s } in
      infinite_tape2 color2 s // could use infinite_tape here
    } in
    infinite_tape2 color1 s
  }
