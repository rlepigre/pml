type rec abc = [A of abc ; B of abc ; C]

// FIXME needs unfolding of fixpoint?
//val rec f : abc ⇒ abc =
//  fun e {
//    case e {
//      A[x] → f B[x]
//      B[x] → f x
//      C    → C
//    }
//  }
