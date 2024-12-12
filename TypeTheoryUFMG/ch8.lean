import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Coprime.Basic

-- Chapter 8

-- Exercises

namespace c8ex1


-- ...This is also the definition of coprime for Mathlib
theorem p (m n : ℕ+) (u : IsCoprime (m : ℤ) n) : ∃x y : ℤ, m * x + n * y = 1 := by
  obtain ⟨a,b,h⟩ := u
  use a; use b
  linarith

theorem ex1 (m n : ℕ+)
  (u : IsCoprime (m:ℤ) n)
  (coprime_symm : IsCoprime (m:ℤ) n → IsCoprime (n:ℤ) m)
  : ∃x y : ℤ, n * x + m * y = 1
  := by
  have v := coprime_symm u
  exact p n m v

theorem ex1' (m n : ℕ+)
  (u : IsCoprime (m:ℤ) n)
  (coprime_symm : IsCoprime (m:ℤ) n → IsCoprime (n:ℤ) m)
  : ∃x y : ℤ, n * x + m * y = 1
  := by
  obtain ⟨a,b,h⟩ := coprime_symm u
  use a; use b;
  linarith

end c8ex1

namespace c8ex6

def greater (x y : Int) := x > y

def eqv (k l m : Int) (_: greater m 0) := ∃x:Int, k-l = x*m

variable (u : greater 5 0)

def p1 := eqv (-3) 17 5 u

def p2 := ¬(eqv (-3) (-17) 5 u)

def refl_eqv (k l m :Int) (u: greater m 0) := eqv k l m u -> eqv l k m u

def iff_eqv (k l m :Int) (u: greater m 0) := eqv k l m u ↔ ∃x:Int,k = l + x*m

end c8ex6
