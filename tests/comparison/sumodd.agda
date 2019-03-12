open import Data.Nat using (_+_; _*_; zero; suc; ℕ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong)
import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
open PropEq.≡-Reasoning

lem1 : (4 + 6 ≡ 10)
lem1 = refl

lem3 : (x : ℕ) → (2 * (x + 4) ≡ 8 + 2 * x)
lem3 = solve 1 (λ x' → con 2 :* (x' :+ con 4) := con 8 :+ con 2 :* x') refl

sum : ℕ → ℕ
sum zero    = 0
sum (suc n) = 1 + 2 * n + sum n

theorem : (n : ℕ) → (sum n ≡ n * n)
theorem 0       = refl
theorem (suc p) =
  begin
    sum (suc p)
  ≡⟨ refl ⟩
    1 + 2 * p + sum p
  ≡⟨ cong (λ x → 1 + 2 * p + x)  (theorem p)⟩
    1 + 2 * p + p * p
  ≡⟨ solve 1 (λ p → con 1 :+ con 2 :* p :+ p :* p := (con 1 :+ p) :* (con 1 :+ p)) refl p ⟩
    (1 + p) * (1 + p)
  ≡⟨ refl ⟩
    (suc p) * (suc p)
  ∎
