def stream⟨a:ο⟩ : ο = νx, lazy⟨{ hd : a; tl : x }⟩

val hd : ∀a:ο, stream⟨a⟩ ⇒ a         = fun s { (force s).hd }
val tl : ∀a:ο, stream⟨a⟩ ⇒ stream⟨a⟩ = fun s { (force s).tl }
