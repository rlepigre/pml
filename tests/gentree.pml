include lib.list

type rec tree⟨c:ο→ο,a:ο⟩ =
  [Nil ; Cons of { hd : a; tl : c⟨tree⟨c,a⟩⟩ }]

type btree⟨a⟩ = tree⟨(a:ο ↦ a × a),a⟩
type ntree⟨a⟩ = tree⟨list,a⟩

val rec genmap : ∀c:ο→ο, (∀a b:ο, (a ⇒ b) ⇒ (c⟨a⟩ ⇒ c⟨b⟩)) ⇒
                    ∀a b:ο, (a ⇒ b) ⇒ tree⟨c,a⟩ ⇒ tree⟨c,b⟩ =
  fun m f t {
    case t {
     [] → Nil
     x::l → f x :: (m (genmap m f) l)
    }
  }

val bmap : ∀a b:ο, (a ⇒ b) ⇒ btree⟨a⟩ ⇒ btree⟨b⟩ =
  genmap (fun f c { (f c.1, f c.2) } : (∀a b:ο, (a ⇒ b) ⇒ (a×a ⇒ b×b)))

val lmap : ∀a b:ο, (a ⇒ b) ⇒ ntree⟨a⟩ ⇒ ntree⟨b⟩ =
  genmap map
