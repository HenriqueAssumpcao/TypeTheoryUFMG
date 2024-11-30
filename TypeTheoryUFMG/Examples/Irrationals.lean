import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
    See [Non-constructive proofs](https://en.wikipedia.org/wiki/Constructive_proof)
    Or [constructive gem](https://math.andrej.com/2009/12/28/constructive-gem-irrational-to-the-power-of-irrational-that-is-rational/)
-/
#check irrational_sqrt_two
lemma not_irrational_two : ¬Irrational 2
  := not_irrational_ofNat 2
#check not_irrational_two
#check Real.rpow_mul
lemma sqrt_two_ge_zero : 0 ≤ √2 := by
  exact Real.sqrt_nonneg 2

#check Real.sq_sqrt

theorem exists_irr_pow_rat
  : ∃ p q : ℝ, Irrational p ∧ Irrational q ∧ ¬Irrational (p^q)
  := by
  by_cases hi : Irrational (√2 ^ √2)
  . use √2 ^ √2
    use √2
    split_ands
    . exact hi
    . exact irrational_sqrt_two
    . clear hi
      have : (√2 ^ √2) ^ √2 = 2 :=
        calc _ = (√2 ^ √2) ^ √2 := rfl
             _ = √2 ^ (√2 * √2) := Real.rpow_mul sqrt_two_ge_zero √2 √2 |>.symm
             _ = √2 ^ (2:ℝ)     := congrArg _ <| Real.mul_self_sqrt zero_le_two
             _ = √2 ^ 2         := Real.rpow_two √2
             _ = 2              := Real.sq_sqrt zero_le_two
      rw [this]
      exact not_irrational_two
  . use √2
    use √2
    split_ands
    . exact irrational_sqrt_two
    . exact irrational_sqrt_two
    . exact hi
