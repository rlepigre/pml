val f : {} =
  case F[{}] of
  | T[x] → ✂
  | F[x] → x

val f : {} =
  case F[{}] of
  | T[x] → {}
  | F[x] → x

val f : [T of {} ; F of {}] ⇒ [T of {} ; F of {}] =
  fun x → 
    case x of
    | T[y] → (case x of | T[y] → F[{}] | F[y] → ✂)
    | F[y] → (case x of | T[y] → ✂ | F[y] → T[{}])
