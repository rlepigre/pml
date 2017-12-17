type cmp = [Ls ; Eq ; Gr]
type cmp' = [Ls ; Eq ; Gr; Bot]

val compose : cmp ⇒ cmp ⇒ cmp' = fun c1 c2 {
  case c1 {
    Ls → case c2 {
      Ls → Ls
      Eq → Ls
      Gr → Bot
    }
    Eq → c2
    Gr → case c2 {
      Ls → Bot
      Eq → Gr
      Gr → Gr
    }
  }
}

type dcmp<a,b> = [Ls ; Eq of a ≡ b ; Gr]
