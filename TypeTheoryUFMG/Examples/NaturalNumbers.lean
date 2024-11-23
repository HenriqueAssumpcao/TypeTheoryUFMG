import Mathlib.Data.Nat.Notation
import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Use

-- Maybe use Naturals without Zero?
#check ℕ+

-- Theorem states if k is sum of two perfect squares
-- then all powers of k are sums of two perfect squares
theorem collares_theorem (k : ℕ) : (∃x y,k=x^2+y^2) →
  ∀ n : ℕ, ∃ x y : ℕ, k ^ n = x ^ 2 + y ^ 2 := by
  intro h n
  induction' n using Nat.twoStepInduction with n hn
  . use 1; use 0; linarith  -- n = 0
  . simp only [pow_one]
    exact h                 -- n = 1
  . obtain ⟨x,y,hn⟩ := hn
    use k * x; use k * y;
    rw [Nat.pow_add, hn]
    linarith

example : ∀ n : ℕ, ∃ x y : ℕ, 13 ^ n = x ^ 2 + y ^ 2 := by
  apply collares_theorem
  use 3; use 2
  linarith
