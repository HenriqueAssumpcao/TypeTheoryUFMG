import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational

namespace TypeTheoryUFMG

-- # 8.1 The nature of definitions
-- **Examples 8.1.1**
-- (1) A rectangle is a quadrilateral with four right angles.
-- ?

-- (2) A function f from R to R is called increasing if, for all x, y ∈ R, x < y implies f (x) < f (y)
def Increasing (f : ℝ → ℝ) := ∀ x y : ℝ, x < y → f x < f y

-- (3) ‘We say that a relation R on a set S is total , if for every two elements x and y of S, either x is related to y, or y to x, or both.
#check Total
-- Total r = ∀ (x y : α), r x y ∨ r y x

-- **Examples 8.1.2**
-- (4) ‘Define c as (1+√5)/2 ’.
noncomputable def c : ℝ := (1 + √5) / 2
-- In this definition, we use the short name c as a handy abbreviation of a more
-- complex expression – thus saving space, and making it easier to speak about
-- the object: after this definition, one may use the name c instead of the longer
-- expression (1+√5) / 2.
-- Hence it is now appropriate to say: ‘It is easy to verify that c^2 − c = 1.’
example : c ^ 2 - c = 1 := sorry

-- (5) ‘Let n be a natural number > 0. Then Dn is defined as the set of all positive integer divisors of n.’
def D (n : ℕ+) := Nat.divisors n

-- Note that D depends on n: we need an n > 0 in order to determine what Dn is
-- So we have that D1 = {1}, D2 = {1, 2}, D3 = {1, 3}, D4 = {1, 2, 4}, . . .
#eval D 1
#eval D 2
#eval D 3
#eval D 4

-- We may use this definition afterwards, e.g. by saying that:
-- ‘D4 ∪ D6 = {1, 2, 3, 4, 6}’,
#eval D 4 ∪ D 6
-- or: ‘if k is a divisor of l, then Dk ⊆ Dl’
example : k ∣ l → D k ⊆ D l := sorry




end TypeTheoryUFMG
