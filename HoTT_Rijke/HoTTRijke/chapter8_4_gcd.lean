/-
  Chapter 8.4 — The greatest common divisor

  We specify what it means to be a greatest common divisor (Definition 8.4.1),
  show that this specification determines the gcd uniquely (Proposition 8.4.2),
  and construct gcd(a, b) with the well-ordering principle of ℕ as the least
  natural number satisfying Definition 8.4.3 (Definition 8.4.6).
-/

import HoTTRijke.chapter8_3_well_ordering

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans

namespace chapter8

/- ###################################################################### -/
/-  Definition 8.4.1 and Proposition 8.4.2                                 -/
/- ###################################################################### -/

-- is-gcd(a, b, d) := Π (x : ℕ), (x ∣ a) × (x ∣ b) ↔ (x ∣ d)
abbrev is_gcd (a b d : myN) : Type :=
  (x : myN) → myEquiv (myProd (dividesT x a) (dividesT x b)) (dividesT x d)

-- Proposition 8.4.2: a greatest common divisor is unique.
def is_gcd_unique (a b d d' : myN) (H : is_gcd a b d) (H' : is_gcd a b d') : d ≡ d' :=
  -- d and d' both divide a and b, hence d ∣ d' and d' ∣ d (Exercise 7.2)
  dividesT_antisymm d d'
    (proj1 (H' d) (proj2 (H d) (dividesT_refl d)))
    (proj1 (H d') (proj2 (H' d') (dividesT_refl d')))


/- ###################################################################### -/
/-  Definition 8.4.3, Proposition 8.4.4 and Lemma 8.4.5                    -/
/- ###################################################################### -/

-- Definition 8.4.3:
-- P(a, b, n) := (a + b ≠ 0) → (n ≠ 0) × Π (x : ℕ), (x ∣ a) × (x ∣ b) → (x ∣ n)
abbrev is_multiple_of_gcd (a b n : myN) : Type :=
  myNegType ((a + b) ≡ myN.zero) →
    myProd (myNegType (n ≡ myN.zero))
           ((x : myN) → myProd (dividesT x a) (dividesT x b) → dividesT x n)

-- Proposition 8.4.4: the family P(a, b) is decidable.
def is_decidable_is_multiple_of_gcd (a b : myN) :
    is_decidable_family (is_multiple_of_gcd a b) :=
  fun n =>
    -- a + b ≠ 0 is decidable; by Proposition 8.2.3 we may assume it holds.
    is_decidable_fun' (is_decidable_neq (a + b) myN.zero) (fun h =>
      is_decidable_prod (is_decidable_neq n myN.zero)
        -- Corollary 8.2.5: common divisors of a and b are bounded by a + b ≠ 0.
        (is_decidable_pi_implication
          (fun x => myProd (dividesT x a) (dividesT x b)) (fun x => dividesT x n)
          (fun x => is_decidable_prod (is_decidable_dividesT x a) (is_decidable_dividesT x b))
          (fun x => is_decidable_dividesT x n)
          (a + b)
          (fun x hx => leqN_of_dividesT x (a + b) h (dividesT_add (proj1 hx) (proj2 hx)))))

-- Lemma 8.4.5: P(a, b, a + b) holds.
def is_multiple_of_gcd_add (a b : myN) : is_multiple_of_gcd a b (a + b) :=
  fun h => myProd.mk h (fun _ hx => dividesT_add (proj1 hx) (proj2 hx))


/- ###################################################################### -/
/-  Definition 8.4.6: the greatest common divisor                          -/
/- ###################################################################### -/

-- The least n : ℕ for which P(a, b, n) holds, by the well-ordering principle.
def gcd_minimal_element (a b : myN) : minimal_element (is_multiple_of_gcd a b) :=
  well_ordering_principle (is_multiple_of_gcd a b) (is_decidable_is_multiple_of_gcd a b)
    ⟨a + b, is_multiple_of_gcd_add a b⟩

def gcdN (a b : myN) : myN := (gcd_minimal_element a b).1

def is_multiple_of_gcd_gcdN (a b : myN) : is_multiple_of_gcd a b (gcdN a b) :=
  proj1 (gcd_minimal_element a b).2

def is_lower_bound_gcdN (a b : myN) : is_lower_bound (is_multiple_of_gcd a b) (gcdN a b) :=
  proj2 (gcd_minimal_element a b).2

-- gcd(a, b) ≤ a + b, by minimality and Lemma 8.4.5.
def gcdN_leq_add (a b : myN) : leqN (gcdN a b) (a + b) :=
  is_lower_bound_gcdN a b (a + b) (is_multiple_of_gcd_add a b)


/- ###################################################################### -/
/-  Lemma 8.4.7 and Theorem 8.4.8                                          -/
/- ###################################################################### -/

-- Lemma 8.4.7: gcd(a, b) = 0 if and only if a + b = 0.
def gcdN_eq_zero_iff (a b : myN) : myEquiv (gcdN a b ≡ myN.zero) ((a + b) ≡ myN.zero) :=
  myProd.mk
    -- If gcd(a, b) = 0, then ¬¬(a + b = 0), and hence a + b = 0 since equality on ℕ
    -- is decidable (Exercise 4.3 (d), `_3_d_i` in chapter4.lean).
    (fun p => chapter4_booleans._3_d_i _ (has_decidable_eq_myN (a + b) myN.zero)
                (fun h => proj1 (is_multiple_of_gcd_gcdN a b h) p))
    -- If a + b = 0, then gcd(a, b) ≤ a + b = 0.
    (fun q => leqN_zero _ (transport (fun y => leqN (gcdN a b) y) q (gcdN_leq_add a b)))

/- The key step of Theorem 8.4.8.  Let g ≠ 0 be a number that is divisible by all
   common divisors of a and b, and which is a lower bound of the family P(a, b).
   Then g divides every number c that is divisible by all common divisors of a and b
   (we use it for c = a and c = b).

   By Euclidean division (Exercise 7.9) we write c = g · q + r with r < g.  Every
   common divisor of a and b divides g · q and c, so it divides r (Proposition 7.1.5).
   If r were nonzero, then r would satisfy P(a, b, r) and hence g ≤ r by minimality,
   contradicting r < g.  So r = 0 and g ∣ c. -/
def dividesT_of_minimal_multiple_of_gcd (a b c g : myN)
    (hg : myNegType (g ≡ myN.zero))
    (hdiv : (x : myN) → myProd (dividesT x a) (dividesT x b) → dividesT x g)
    (hmin : is_lower_bound (is_multiple_of_gcd a b) g)
    (hc : (x : myN) → myProd (dividesT x a) (dividesT x b) → dividesT x c) :
    dividesT g c :=
  match euclidean_division g hg c with
  | ⟨q, r, myProd.mk hr e⟩ =>
      let hr_div : (x : myN) → myProd (dividesT x a) (dividesT x b) → dividesT x r :=
        fun x hx =>
          @dividesT_add_cancel_left x (g * q) r
            (dividesT_mul_right q (hdiv x hx))
            (transport (fun y => dividesT x y) e (hc x hx))
      match has_decidable_eq_myN r myN.zero with
      | Sum.inl r0 => ⟨q, myEq_symm (e • (ap (fun y => (g * q) + y) _ _ r0))⟩
      | Sum.inr rn0 =>
          Empty.elim (not_ltN_of_leqN r g (hmin r (fun _ => myProd.mk rn0 hr_div)) hr)

-- Theorem 8.4.8: gcd(a, b) is a greatest common divisor of a and b.
def is_gcd_gcdN (a b : myN) : is_gcd a b (gcdN a b) :=
  match has_decidable_eq_myN (a + b) myN.zero with
  | Sum.inl h =>
      -- a + b = 0: then a = 0, b = 0 and gcd(a, b) = 0, and every x divides 0.
      let ha : a ≡ myN.zero := proj1 (addN_eq_zero a b h)
      let hb : b ≡ myN.zero := proj2 (addN_eq_zero a b h)
      let hg : gcdN a b ≡ myN.zero := proj2 (gcdN_eq_zero_iff a b) h
      fun x => myProd.mk
        (fun _ => transport (fun y => dividesT x y) (myEq_symm hg) (dividesT_zero x))
        (fun _ => myProd.mk
                    (transport (fun y => dividesT x y) (myEq_symm ha) (dividesT_zero x))
                    (transport (fun y => dividesT x y) (myEq_symm hb) (dividesT_zero x)))
  | Sum.inr h =>
      -- a + b ≠ 0: then gcd(a, b) ≠ 0 by Lemma 8.4.7.
      let hg : myNegType (gcdN a b ≡ myN.zero) := fun p => h (proj1 (gcdN_eq_zero_iff a b) p)
      let hdiv := proj2 (is_multiple_of_gcd_gcdN a b h)
      let hmin := is_lower_bound_gcdN a b
      fun x => myProd.mk
        (hdiv x)
        -- If x ∣ gcd(a, b), then x ∣ a and x ∣ b, since gcd(a, b) divides a and b.
        (fun p => myProd.mk
          (dividesT_trans p (dividesT_of_minimal_multiple_of_gcd a b a (gcdN a b) hg hdiv hmin
                                (fun _ hx => proj1 hx)))
          (dividesT_trans p (dividesT_of_minimal_multiple_of_gcd a b b (gcdN a b) hg hdiv hmin
                                (fun _ hx => proj2 hx))))

-- In particular gcd(a, b) divides a and b.
def gcdN_dividesT_left (a b : myN) : dividesT (gcdN a b) a :=
  proj1 (proj2 (is_gcd_gcdN a b (gcdN a b)) (dividesT_refl _))

def gcdN_dividesT_right (a b : myN) : dividesT (gcdN a b) b :=
  proj2 (proj2 (is_gcd_gcdN a b (gcdN a b)) (dividesT_refl _))


-- The gcd can be computed.
example : (gcdN _4 _6) ≡ _2 := MyEq.refl _
example : (gcdN _0 _5) ≡ _5 := MyEq.refl _

end chapter8
