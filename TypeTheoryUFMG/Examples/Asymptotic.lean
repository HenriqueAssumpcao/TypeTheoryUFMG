import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.NthRewrite
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
#check Nat.le_trans
#check Nat.add_mul
#check Nat.one_mul
#check Nat.add_le_add_left
#check Nat.le_of_mul_le_mul_left
#check Nat.mul_le_mul_left

-- Prove:
-- n² + 2n is O(n²)
example : O (λn↦n^2 + 2*n) (λn↦n^2) := by
  unfold O
  simp only [ge_iff_le]
  use 3
  use 2
  intro n nge2
  apply @Nat.le_trans (n ^ 2 + 2 * n) (n ^ 2 + 2 * n ^ 2) (3 * n ^ 2)
  . apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    rw [Nat.pow_two]
    nth_rewrite 1 [←Nat.one_mul n]
    apply Nat.mul_le_mul_right
    exact Nat.le_of_succ_le nge2
  . apply Nat.le_of_eq
    nth_rewrite 1 [←Nat.one_mul (n^2)]
    rw [←Nat.add_mul]


end Asymptotic
