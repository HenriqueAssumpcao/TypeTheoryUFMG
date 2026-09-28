/-
  Chapter 8.6 — Boolean reflection

  A decision d : is-decidable(A) can be turned into a boolean.  The boolean
  reflection principle (Theorem 8.6.2) says that an identification
  booleanization(d) = true yields an element of A.  Since `MyEq.refl` type checks
  whenever booleanization(d) *computes* to true, this lets the proof assistant
  verify, e.g., that 37 is prime by running the decision procedure of
  Proposition 8.5.2 (Remark 8.6.3).

  Booleans are the type `myBool` of chapter3.lean, and the fact that
  false ≠ true is Exercise 6.2, proved in chapter6.lean.
-/

import HoTTRijke.chapter8_5_primes

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans

namespace chapter8

/- ###################################################################### -/
/-  Definition 8.6.1                                                       -/
/- ###################################################################### -/

def booleanization {A : Type} : is_decidable A → myBool
  | Sum.inl _ => myBool.myTrue
  | Sum.inr _ => myBool.myFalse


/- ###################################################################### -/
/-  Theorem 8.6.2: the boolean reflection principle                        -/
/- ###################################################################### -/

-- Exercise 6.2: there is a map (false = true) → ∅.
-- (`Eq_bool_equiv_conv` of chapter6.lean maps false = true to Eq_bool(false, true) ≐ ∅.)
def myFalse_neq_myTrue : myNegType (myBool.myFalse ≡ myBool.myTrue) :=
  fun p => chapter6_Universes.Eq_bool_equiv_conv myBool.myFalse myBool.myTrue p

-- reflect(inl(a), p) := a   and   reflect(inr(f), p) := ex-falso(α(p))
def reflect {A : Type} : (d : is_decidable A) → (booleanization d ≡ myBool.myTrue) → A
  | Sum.inl a, _ => a
  | Sum.inr _, p => Empty.elim (myFalse_neq_myTrue p)

-- reflect(inl(a)) ≐ a
def reflect_inl {A : Type} (a : A) : (reflect (Sum.inl a) (MyEq.refl _)) ≡ a :=
  MyEq.refl _

-- Conversely, the booleanization of a decision of an inhabited type is true.
def booleanization_eq_true {A : Type} : (d : is_decidable A) → A → (booleanization d ≡ myBool.myTrue)
  | Sum.inl _, _ => MyEq.refl _
  | Sum.inr f, a => Empty.elim (f a)


/- ###################################################################### -/
/-  Remark 8.6.3                                                           -/
/- ###################################################################### -/

/- The following elements of is-prime(7) and is-prime(37) contain no explicit
   information as to *why* the numbers are prime: they type check because the
   decision procedure `is_decidable_is_prime` evaluates to an element of the form
   `Sum.inl _`, so that `MyEq.refl myTrue` is an identification
   booleanization(d(p)) = true.  Lean has to run the decision procedure on unary
   natural numbers to check this; for 37 this takes several seconds. -/

def is_prime_7 : is_prime _7 :=
  reflect (is_decidable_is_prime _7) (MyEq.refl _)

def _37 : myN := ofNatN 37

def is_prime_37 : is_prime _37 :=
  reflect (is_decidable_is_prime _37) (MyEq.refl _)

-- Boolean reflection also proves negative statements: 9 is not prime.
def is_not_prime_9 : myNegType (is_prime _9) :=
  reflect (is_decidable_neg (is_decidable_is_prime _9)) (MyEq.refl _)

/- All constructions of this chapter are programs, so they can also be run with
   `#eval`, e.g.

     #eval toNatN (collatz (ofNatN 27))                  -- 82
     #eval toNatN (gcdN (ofNatN 84) (ofNatN 36))         -- 12
     #eval toNatN (infinitude_of_primes _4).1            -- 7

   (keep the arguments of `infinitude_of_primes` small: its witness (n+1)! + 1 is
   computed in unary.) -/

end chapter8
