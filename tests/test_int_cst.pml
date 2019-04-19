include lib.int

val t1 : int ⇒ int = fun n { n - 2 } // not ambiguous

val t2 : int ⇒ int = fun n { n - -2 } // not ambiguous
