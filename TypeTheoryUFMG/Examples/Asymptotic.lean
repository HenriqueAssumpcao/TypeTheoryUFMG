import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Set
import Mathlib.Tactic.Use

namespace Asymptotic
-- f(n) is O(g(n))
-- if exists c n0
-- s.t. forall n >= n0,
-- f n <= c * g n
def O (f g : ℕ → ℕ) : Prop :=
  ∃ c n₀ : ℕ,
  ∀ n : ℕ, (n ≥ n₀)
  → f n <= c * g n

#check O (λx↦x) (λx↦x)

-- Prove:
-- n² + 2n is O(n²)
example : O (λn↦n^2 + 2*n) (λn↦n^2) := by
  unfold O
  simp only [ge_iff_le]
  use 3
  use 2
  intro n nge2
  calc
   _ = n ^ 2 + 2 * n  := rfl
   _ ≤ n ^ 2 + n ^ 2  := by simp [Nat.pow_two, Nat.mul_le_mul_right n nge2]
   _ = 2 * n ^ 2      := by simp [Nat.two_mul]
   _ ≤ 3 * n ^ 2      := by simp [Nat.mul_le_mul]

end Asymptotic
