import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational

namespace TypeTheoryUFMG

-- # 8.1 The nature of definitions
-- **Examples 8.1.1**
-- (1) A `rectangle` is a quadrilateral with four right angles.
-- ?

-- (2) A function f from R to R is called `increasing` if, for all x, y ∈ R, x < y implies f (x) < f (y)
def Increasing (f : ℝ → ℝ) := ∀ x y : ℝ, x < y → f x < f y

-- (3) ‘We say that a relation R on a set S is `total` , if for every two elements x and y of S, either x is related to y, or y to x, or both.
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
theorem c_sq_sub_c_eq_one : c ^ 2 - c = 1 := calc
  _ = c ^ 2 - c                       := rfl
  _ = c ^ (2:ℝ) - c                   := by rw[Real.rpow_two c |>.symm]
  _ = (1 + √5)^(2:ℝ) / 2^(2:ℝ) - c    := by have : c ^ (2:ℝ) = (1 + √5)^(2:ℝ) / 2^(2:ℝ) := Real.div_rpow
                                                (add_nonneg (zero_le_one' ℝ) (Real.sqrt_nonneg 5))
                                                (zero_le_two) (2:ℝ); rw [this]
  _ = (1 + √5)^2 / 2^(2:ℝ) - c        := by rw[Real.rpow_two]
  _ = (1 + 2*√5 + √5^2) / 4 - c       := by linarith
  _ = (1 + 2*√5 + 5) / 4 - c          := by rw [Real.sq_sqrt (Nat.ofNat_nonneg' 5)]
  _ = (6 + 2*√5) / 4 - c              := by linarith
  _ = (6 + 2*√5) / 4 - (1 + √5) / 2   := by rfl
  _ = 1                               := by linarith

lemma c_sq_is_succ_c : c ^ 2 = c + 1 := by
  have : c ^ 2 - c = 1 := c_sq_sub_c_eq_one
  linarith

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
example : k ∣ l → D k ⊆ D l :=
  λ dvd => Nat.divisors_subset_of_dvd (PNat.ne_zero l) (PNat.dvd_iff.mp dvd)


-- # 8.4 Instantiations of definitions
-- Obviously, definitions are not made for their own sake, but in order to be used .
-- For example, we have already mentioned that the definition c := (1+√5) / 2 may
-- be used to state that c^2 − c = 1, which is easier to read than
-- (1+√5) / 2)^2 − (1+√5)/2 = 1 .
-- Moreover, the same c may be used over and over again, for example in the following calculation:
-- ‘Since c2 = c + 1, we have that c^3 = c^2 + c = c + 1 + c = 2c + 1 ’,
example (h : c^2 = c + 1) : c^3 = 2*c + 1 := by calc
    _ = c^2 * c := by linarith
    _ = 2*c + 1 := by simp[c_sq_is_succ_c]; linarith

-- or in establishing that
-- ‘The n-th Fibonacci number fn satisfies the equation fn = (c^n−(1−c)^n)/√5 .’
#check @Nat.odd_iff 3 |>.mpr
example : Odd 3 := @Nat.odd_iff 3 |>.mpr rfl
#check Odd.pow_neg (@Nat.odd_iff 3 |>.mpr rfl)
--  (Nat.odd_iff  |>.mpr rfl)

#check mul_lt_mul_left
#check div_lt_div_right

-- ‘The function sending a real number to its third power, is increasing.’
example : Increasing (λ x : ℝ ↦ x^3) := by
  intro x y x_lt_y
  simp
  by_cases hxz : x = 0
  . simp [hxz] at *
    exact pow_pos x_lt_y 3
  apply lt_or_gt_of_ne at hxz
  obtain ⟨r,hr0,hr⟩ := exists_pos_add_of_lt' x_lt_y
  cases' hxz with hxlt0 hxgt0
  .
    by_cases hrx : r < -x
    . rw [←hr,(by linarith : (x+r)^3 = x^3 + (3*x^2*r + 3*x*r^2 + r^3))]
      suffices 0 < r * (3 * x ^ 2 + 3 * x * r + r ^ 2) by linarith
      suffices 0 < 3 * x ^ 2 + 3 * x * r + r ^ 2 by exact mul_pos hr0 this
      suffices 0 < 3 * x ^ 2 + 3 * x * r by exact add_pos' this (sq_pos_of_pos hr0)
      suffices 0 < x ^ 2 + x * r by linarith
      sorry

    have oracle : 0 ≤ y := sorry -- by exact? -- from r ≥ -x
    have y_cb_nneg : 0 ≤ y ^ 3 := pow_nonneg oracle 3
    have x_cb_ltz : x ^ 3 < 0 := Odd.pow_neg (@Nat.odd_iff 3 |>.mpr rfl) hxlt0
    exact gt_of_ge_of_gt y_cb_nneg x_cb_ltz

  rw [←hr]
  have : (x+r)^3 = x^3 + (3*x^2*r + 3*x*r^2 + r^3) := by linarith
  rw [this]
  nth_rewrite 1 [AddMonoid.add_zero (x^3) |>.symm]
  apply (Real.add_lt_add_iff_left (x^3)).mpr
  have x_sq_3_r_pos : 0 < 3 * x ^ 2 * r := mul_pos (mul_pos three_pos <| pow_two_pos_of_ne_zero <| ne_of_lt hxgt0 |>.symm) hr0
  have r_cb_pos : 0 < r ^ 3 := pow_pos hr0 3
  have t2 : 0 < 3 * x * r ^ 2 := mul_pos (mul_pos three_pos hxgt0) <|sq_pos_of_pos hr0
  exact add_pos' (add_pos' x_sq_3_r_pos t2) r_cb_pos

-- One says: ‘f has been instantiated with λx : R . x3 ’

-- For example, let’s take for S the set R of the reals, and for R the relation `≤`
-- on that set R. Then we obtain the correct instantiation
-- total (R, ≤) .
#check @Total ℝ (·≤·)
-- This is a proposition, which does indeed hold in mathematics.

-- Instantiating S with N+, the positive naturals, and R with ‘|’, the divisibility
-- relation on N+, we obtain
-- total (N+, | ).
#check @Total ℕ+ (·∣·)

-- As an instantiation, this is correct, again. (Which has got nothing to do with
-- the fact that, as a proposition, it is false: for example, neither 3|5, nor 5|3.)

-- # 8.5 A formal format for definitions
-- As an example, we have listed a series of definitions regarding a set S and a relation R on S in Figure 8.2.
-- The notions `reflexive`, `antisymmetric` and `transitive` have been formally expressed here
#check Reflexive
-- ∀ (a : α), r a a
#check AntiSymmetric
-- ∀ (a b : α), r a b → r b a → a = b
#check Transitive
-- ∀ (a b c : α), r a b → r b c → r a c

-- by means of defined constants, and so is their conjunction: `partially-ordered`

#check PartialOrder


-- All four definitions depend on the same context, and therefore we suffice with one initial pair of context flags.  Since each of the four defined notions is a proposition, they all have type ∗

-- # 8.6 Definitions depending on assumptions
-- ‘Let S be a set, partially ordered by a relation R. An element m of S is
-- called a minimal element with respect to R, if R(x, m) implies that x = m.’
#check IsLeast
-- `a` is a least element of a set `s`; for a partial order, it is unique if exists

example : IsLeast (Set.univ : Set ℕ) 0 := by
  split_ands
  . trivial
  . intro a an
    exact Nat.zero_le a

example : IsLeast (Set.univ : Set ℕ) 0 :=
  ⟨Set.mem_univ 0
  , λ a _ => Nat.zero_le a ⟩

-- # 8.7 Giving names to proofs

-- * Theorem. Let m and n be positive natural numbers and assume that they are `coprime`.
-- Then there are integers x and y such that mx + ny = 1.’

#check Nat.gcd_eq_gcd_ab
-- Bézout's lemma: given x y : ℕ, gcd x y = x * a + y * b, where a = gcd_a x y and b = gcd_b x y are computed by the extended Euclidean algorithm



end TypeTheoryUFMG
