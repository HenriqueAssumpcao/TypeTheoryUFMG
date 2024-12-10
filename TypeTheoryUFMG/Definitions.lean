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


-- # 8.4 Instantiations of definitions
-- Obviously, definitions are not made for their own sake, but in order to be used .
-- For example, we have already mentioned that the definition c := (1+√5) / 2 may
-- be used to state that c^2 − c = 1, which is easier to read than
-- (1+√5) / 2)^2 − (1+√5)/2 = 1 .
-- Moreover, the same c may be used over and over again, for example in the following calculation:
-- ‘Since c2 = c + 1, we have that c^3 = c^2 + c = c + 1 + c = 2c + 1 ’,
example (h : c^2 = c + 1) : c^3 = 2*c + 1
  := by calc
    _ = c ^ 3      := rfl
    _ = c^2 + c    := sorry
    _ = c + 1 + c  := congrFun (congrArg HAdd.hAdd h) c
    _ = 2*c + 1    := sorry

-- or in establishing that
-- ‘The n-th Fibonacci number fn satisfies the equation fn = (c^n−(1−c)^n)/√5 .’

-- ‘The function sending a real number to its third power, is increasing.’
example : Increasing (λ x : ℝ ↦ x^3) := sorry
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
