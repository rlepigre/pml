
type nat_sig_aux⟨a:ο⟩ =
  { z : a; s : a ⇒ a; r : a ⇒ ∀p,(p ⇒ p) ⇒ p ⇒ p  }

type nat_sig = ∃a:ο, nat_sig_aux⟨a⟩

type rec nat = [ Zero ; S of nat ]

val nat_nat:nat_sig =
  { z = (Zero : nat)
  ; s = (fun x { S[x] } : nat ⇒ nat)
  ; r = (let rec r : nat ⇒ ∀p,(p ⇒ p) ⇒ p ⇒ p =
            fun n f a { case n { Zero → a S[m] → r m f (f a) } }; r)
  }

type cnat = ∀p,(p ⇒ p) ⇒ (p ⇒ p)

val nat_cnat:nat_sig =
  { z = (fun f x { x } : cnat)
  ; s = (fun n f x { f (n f x) } : cnat ⇒ cnat)
  ; r = (fun n { n } : cnat ⇒ ∀p,(p ⇒ p) ⇒ p ⇒ p )
  }


val translate : ∀a:ο, ∀b:ο, nat_sig_aux⟨a⟩ ⇒ nat_sig_aux⟨b⟩ ⇒ a ⇒ b =
  fun s1 s2 a { s1.r a s2.s s2.z }

val deux_cnat : cnat = nat_nat.r (nat_nat.s (nat_nat.s nat_nat.z))

val deux_cnat_bis : cnat = nat_cnat.r (translate nat_nat nat_cnat
                                         (nat_nat.s (nat_nat.s nat_nat.z)))

val deux_cnat_ter : cnat = nat_nat.r (translate nat_cnat nat_nat
                                         (nat_cnat.s (nat_cnat.s nat_cnat.z)))

val zero : nat_sig ⇒ ∀p,(p ⇒ p) ⇒ (p ⇒ p) =
  fun s g b {
    s.r s.z g b
  }

val deux : nat_sig ⇒ ∀p,(p ⇒ p) ⇒ (p ⇒ p) =
  fun s f a { s.r (s.s (s.s s.z)) f a }

val succ : ∀a, nat_sig_aux⟨a⟩ ⇒ a ⇒ cnat =
  fun s x { s.r (s.s x) }

val test : cnat = succ nat_nat nat_nat.z