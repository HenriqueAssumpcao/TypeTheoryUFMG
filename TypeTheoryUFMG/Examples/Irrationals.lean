import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- See [Non-constructive proofs](https://en.wikipedia.org/wiki/Constructive_proof) 
-- Or [constructive gem](https://math.andrej.com/2009/12/28/constructive-gem-irrational-to-the-power-of-irrational-that-is-rational/)
#check irrational_sqrt_two
lemma not_irrational_two : ¬Irrational 2
  := not_irrational_ofNat 2
#check not_irrational_two

theorem exists_irr_pow_rat
  : ∃ p q : ℝ, Irrational p ∧ Irrational q ∧ ¬Irrational (p^q)  
  := by
  sorry

