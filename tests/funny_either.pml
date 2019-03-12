include lib.either

type e⟨a,b⟩ = ∀x∈bool, either⟨a | x ≡ true, b | x ≡ false⟩
