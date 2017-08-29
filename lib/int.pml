// Normalized integers
type rec pos = [Z; S of pos]
type rec neg = [Z; P of neg]
type int = [Z; S of pos; P of neg]
// Non normalised
type rec nint = [Z; S of nint; P of nint]

check int ⊂ nint

val suc : int ⇒ int = fun n {
  case n {
    Z    → S[Z]
    S[n] → S[S[n]]
    P[n] → n
  }
}

val pre : int ⇒ int = fun n {
  case n {
    Z    → P[Z]
    P[n] → P[P[n]]
    S[n] → n
  }
}

// FIXME? should work or stupid mistake ?
def icase⟨p:ι→τ,q:ι→τ,n:ι⟩ = case n { Z → {} | S[n] → p⟨n⟩ | P[n] → q⟨n⟩ }
def ncase⟨p:ι→τ,n:ι⟩ = case n { Z → {} | S[n] → p⟨n⟩ }
def pcase⟨p:ι→τ,n:ι⟩ = case n { Z → {} | P[n] → p⟨n⟩ }

val suc_pre : ∀n∈int, suc (pre n) ≡ n = fun n { icase⟨ncase⟨(x:ι)↦{}⟩,(x:ι)↦{},n⟩ }

def icase⟨n⟩ = case n { Z → {} | S[_] → {} | P[_] → {} }
def ncase⟨n⟩ = case n { Z → {} | S[_] → {} }
def pcase⟨n⟩ = case n { Z → {} | P[_] → {} }

val suc_pre : ∀n∈int, suc (pre n) ≡ n = fun n {
  case n {
    Z → {}
    S[p] → ncase⟨p⟩
    P[_] → {}
  }
}
val pre_suc : ∀n∈int, pre (suc n) ≡ n = fun n {
  case n {
    Z → {}
    S[_] → {}
    P[p] → pcase⟨p⟩
  }
}

val p0 : int = Z
val p1 : int = suc p0
val p2 : int = suc p1
val p3 : int = suc p2
val p4 : int = suc p3
val p5 : int = suc p4
val n1 : int = pre p0
val n2 : int = pre p1
val n3 : int = pre p2
val n4 : int = pre p3
val n5 : int = pre p4

val rec add : int ⇒ int ⇒ int = fun n m {
  case n {
    Z    → m
    S[n] → suc (add n m)
    P[n] → pre (add n m)
  }
}

val rec sub : int ⇒ int ⇒ int = fun n m {
  case m {
    Z    → m
    S[m] → pre (sub n m)
    P[m] → suc (sub n m)
  }
}
val rec dbl : int ⇒ int = fun n {
  case n {
    Z → Z
    S[n] → suc (suc (dbl n))
    P[n] → pre (pre (dbl n))
  }
}
val rec mul : int ⇒ int ⇒ int = fun n m {
  case m {
    Z → Z
    S[m] → add (mul n m) n
    P[m] → sub (mul n m) n
  }
}
val sgn : int ⇒ int = fun n {
  case n {
    Z → Z
    S[_] → p1
    P[_] → n1
  }
}
val rec even : int ⇒ bool = fun n {
  case n {
    Z → true
    S[n] → case n {
      Z → false
      S[n] → even n
    }
    P[n] → case n {
      Z → false
      P[n] → even n
    }
  }
}
val rec le : int ⇒ int ⇒ bool = fun n m {
  let d = sub m n;
  case d {
    Z → true
    S[_] → true
    P[_] → false
  }
}
val rec ge : int ⇒ int ⇒ bool = fun n m { le m n }
val rec lt : int ⇒ int ⇒ bool = fun n m {
  let d = sub m n;
  case d {
    Z → false
    S[_] → true
    P[_] → false
  }
}
val rec gt : int ⇒ int ⇒ bool = fun n m { lt m n }
