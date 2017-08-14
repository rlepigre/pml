val f : {} =
  case F[{}] {
    T[x] → ✂
    F[x] → x
  }

val f : {} =
  case F[{}] {
    T[x] → {}
    F[x] → x
  }

val f : [T of {} ; F of {}] ⇒ [T of {} ; F of {}] =
  fun x { 
    case x {
      T[y] → case x { T[y] → F[{}] | F[y] → ✂     }
      F[y] → case x { T[y] → ✂     | F[y] → T[{}] }
    }
  }
