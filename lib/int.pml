// Normalized integers
type rec pos = [Zero; S of pos]
type rec neg = [Zero; P of neg]
type int = [Zero; S of pos; P of neg]
// Non normalised
type rec nint = [Zero; S of nint; P of nint]

assert int ⊂ nint

val suc : int ⇒ int = fun n {
  case n {
    Zero → S[Zero]
    S[n] → S[S[n]]
    P[n] → n
  }
}

val pre : int ⇒ int = fun n {
  case n {
    Zero → P[Zero]
    P[n] → P[P[n]]
    S[n] → n
  }
}

def icase⟨p:ι→τ,q:ι→τ,n:ι⟩ = case n { Zero → {} | S[n] → p⟨n⟩ | P[n] → q⟨n⟩ }
def ncase⟨p:ι→τ,n:ι⟩ = case n { Zero → {} | S[n] → p⟨n⟩ }
def pcase⟨p:ι→τ,n:ι⟩ = case n { Zero → {} | P[n] → p⟨n⟩ }

val suc_pre : ∀n∈int, suc (pre n) ≡ n =
  fun n { icase⟨ncase⟨(x:ι↦{})⟩,(x:ι↦{}),n⟩ }

def icase⟨n⟩ = case n { Zero → {} | S[_] → {} | P[_] → {} }
def ncase⟨n⟩ = case n { Zero → {} | S[_] → {} }
def pcase⟨n⟩ = case n { Zero → {} | P[_] → {} }

val p0 : int = Zero
val p1 : int = suc p0
val p2 : int = suc p1
val p3 : int = suc p2
val p4 : int = suc p3
val p5 : int = suc p4
val n1 : int = pre p0
val n2 : int = pre n1
val n3 : int = pre n2
val n4 : int = pre n3
val n5 : int = pre n4

// Addition function.
infix (+) = add priority 3 left associative

val rec (+) : int ⇒ int ⇒ int = fun n m {
  case n {
    Zero → m
    S[n] → suc (n + m)
    P[n] → pre (n + m)
  }
}

// Difference function.
infix (-) = minus priority 3 left associative

val rec (-) : int ⇒ int ⇒ int = fun n m {
  case m {
    Zero → n
    S[m] → pre (n - m)
    P[m] → suc (n - m)
  }
}

// double
val rec dbl : int ⇒ int = fun n {
  case n {
    Zero → Zero
    S[n] → suc (suc (dbl n))
    P[n] → pre (pre (dbl n))
  }
}

// Multiplication function.
infix (*) = mul priority 2 left associative

val rec (*) : int ⇒ int ⇒ int = fun n m {
  case m {
    Zero → Zero
    S[m] → n * m + n
    P[m] → n * m - n
  }
}
val sgn : int ⇒ [P;Z;S] = fun n {
  case n {
    Zero → Z
    S[_] → S
    P[_] → P
  }
}
val rec even : int ⇒ bool = fun n {
  case n {
    Zero → true
    S[n] → case n {
      Zero → false
      S[n] → even n
    }
    P[n] → case n {
      Zero → false
      P[n] → even n
    }
  }
}
val rec le : int ⇒ int ⇒ bool = fun n m {
  let d = m - n;
  case d {
    Zero → true
    S[_] → true
    P[_] → false
  }
}

val rec ge : int ⇒ int ⇒ bool = fun n m { le m n }

val rec lt : int ⇒ int ⇒ bool = fun n m {
  let d = m - n;
  case d {
    Zero → false
    S[_] → true
    P[_] → false
  }
}
val rec gt : int ⇒ int ⇒ bool = fun n m { lt m n }

include lib.nat

assert nat ⊂ int
