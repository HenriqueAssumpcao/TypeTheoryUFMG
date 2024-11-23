import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory intervalIntegral Interval

theorem integral_of_linear (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

theorem integral_of_squared (a b : ℝ) : (∫ x in a..b, x ^ 2) = (b ^ 3 - a ^ 3) / 3 := by
  simp only [integral_pow, Nat.reduceAdd, Nat.cast_ofNat,two_add_one_eq_three]

example : (∫ x in (0:ℝ)..(9:ℝ), x ^ 2) = 243 := by
  rw [integral_of_squared (0:ℝ) (9:ℝ)]
  linarith

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h
