/-
  Chapter 8.5 — The infinitude of primes

  We define proper divisors and prime numbers (Definition 8.5.1), show that being
  prime is decidable (Proposition 8.5.2), and prove that there are infinitely many
  primes (Theorem 8.5.6): for every n, the least a > n that is not divisible by any
  number 2 ≤ x ≤ n exists by the well-ordering principle (with n! + 1 as a witness),
  and it is a prime.
-/

import HoTTRijke.chapter8_4_gcd

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans

namespace chapter8

/- ###################################################################### -/
/-  Definition 8.5.1                                                       -/
/- ###################################################################### -/

-- (i) d is a proper divisor of n:  (d ≠ n) × (d ∣ n)
abbrev is_proper_divisor (n d : myN) : Type :=
  myProd (myNegType (d ≡ n)) (dividesT d n)

-- (ii) n is prime:  Π (x : ℕ), is-proper-divisor(n, x) ↔ (x = 1)
abbrev is_prime (n : myN) : Type :=
  (x : myN) → myEquiv (is_proper_divisor n x) (x ≡ _1)


/- ###################################################################### -/
/-  Proposition 8.5.2: being prime is decidable                            -/
/- ###################################################################### -/

-- is-prime'(n) := (n ≠ 1) × Π (x : ℕ), is-proper-divisor(n, x) → (x = 1)
abbrev is_prime' (n : myN) : Type :=
  myProd (myNegType (n ≡ _1)) ((x : myN) → is_proper_divisor n x → (x ≡ _1))

def is_prime'_of_is_prime (n : myN) (H : is_prime n) : is_prime' n :=
  myProd.mk
    -- if n = 1, then 1 would be a proper divisor of 1, i.e. 1 ≠ 1
    (fun p => proj1 (proj2 (H _1) (MyEq.refl _1)) (myEq_symm p))
    (fun x h => proj1 (H x) h)

def is_prime_of_is_prime' (n : myN) (H : is_prime' n) : is_prime n :=
  fun x => myProd.mk
    (proj2 H x)
    -- since n ≠ 1, the number 1 is a proper divisor of n
    (fun p => transport (fun y => is_proper_divisor n y) (myEq_symm p)
                (myProd.mk (fun q => proj1 H (myEq_symm q)) (one_dividesT n)))

def is_prime_iff_is_prime' (n : myN) : myEquiv (is_prime n) (is_prime' n) :=
  myProd.mk (is_prime'_of_is_prime n) (is_prime_of_is_prime' n)

def is_decidable_is_proper_divisor (n : myN) : is_decidable_family (is_proper_divisor n) :=
  fun x => is_decidable_prod (is_decidable_neq x n) (is_decidable_dividesT x n)

def two_neq_one : myNegType (_2 ≡ _1) :=
  fun p => succN_neq_zero _0 (succN_inj p)

def is_decidable_is_prime' (n : myN) : is_decidable (is_prime' n) :=
  match has_decidable_eq_myN n myN.zero with
  | Sum.inl h =>
      -- Every nonzero number, e.g. 2, is a proper divisor of 0, so 0 is not prime.
      Sum.inr (fun H =>
        two_neq_one (proj2 (transport is_prime' h H) _2
                      (myProd.mk (succN_neq_zero _1) (dividesT_zero _2))))
  | Sum.inr h =>
      is_decidable_prod (is_decidable_neq n _1)
        -- Corollary 8.2.5: proper divisors of n ≠ 0 are bounded by n.
        (is_decidable_pi_implication (is_proper_divisor n) (fun x => x ≡ _1)
          (is_decidable_is_proper_divisor n) (fun x => has_decidable_eq_myN x _1)
          n (fun x hx => leqN_of_dividesT x n h (proj2 hx)))

-- Proposition 8.5.2
def is_decidable_is_prime (n : myN) : is_decidable (is_prime n) :=
  is_decidable_of_iff (myProd.mk (is_prime_of_is_prime' n) (is_prime'_of_is_prime n))
    (is_decidable_is_prime' n)


/- ###################################################################### -/
/-  Definition 8.5.3, Lemma 8.5.4 and Lemma 8.5.5                          -/
/- ###################################################################### -/

-- F(n, a) := (n < a) × Π (x : ℕ), (x ≤ n) → ((x ∣ a) → (x = 1))
abbrev in_sieve_of_eratosthenes (n a : myN) : Type :=
  myProd (ltN n a) ((x : myN) → leqN x n → dividesT x a → (x ≡ _1))

-- Lemma 8.5.4: F(n, a) is decidable.
def is_decidable_in_sieve_of_eratosthenes (n : myN) :
    is_decidable_family (in_sieve_of_eratosthenes n) :=
  fun a => is_decidable_prod (is_decidable_ltN n a)
    (is_decidable_pi_implication (fun x => leqN x n) (fun x => dividesT x a → (x ≡ _1))
      (fun x => is_decidable_leqN x n)
      (fun x => is_decidable_fun (is_decidable_dividesT x a) (has_decidable_eq_myN x _1))
      n (fun _ h => h))

-- Lemma 8.5.5: F(n, n! + 1) holds.
def in_sieve_of_eratosthenes_factorial_succ (n : myN) :
    in_sieve_of_eratosthenes n (myN.succ (factorial n)) :=
  myProd.mk
    -- n < n! + 1, because n ≤ n!
    (ltN_succ_of_leqN n (factorial n) (leqN_factorial n))
    (fun x hx p =>
      -- x ≠ 0, because 0 does not divide n! + 1
      let hx0 : myNegType (x ≡ myN.zero) := fun q =>
        succN_neq_zero _ (eq_zero_of_zero_dividesT _
          (transport (fun y => dividesT y (myN.succ (factorial n))) q p))
      -- x ∣ n! (Exercise 7.3), hence x ∣ 1 (Proposition 7.1.5), hence x = 1
      eq_one_of_dividesT_one x
        (@dividesT_add_cancel_left x (factorial n) _1 (dividesT_factorial n x hx0 hx) p))


/- ###################################################################### -/
/-  Theorem 8.5.6: there are infinitely many primes                        -/
/- ###################################################################### -/

/- Let n' := n + 1 (which is nonzero), and let p be the least number with F(n', p).
   Then p is prime and n < p. -/
def infinitude_of_primes (n : myN) : Σ p : myN, myProd (is_prime p) (ltN n p) :=
  let n' := myN.succ n
  match well_ordering_principle (in_sieve_of_eratosthenes n')
          (is_decidable_in_sieve_of_eratosthenes n')
          ⟨myN.succ (factorial n'), in_sieve_of_eratosthenes_factorial_succ n'⟩ with
  | ⟨p, myProd.mk (myProd.mk hlt hdiv) hmin⟩ =>
      -- p ≠ 0 and p ≠ 1, because n + 1 < p
      let hp0 : myNegType (p ≡ myN.zero) := fun q => transport (ltN n') q hlt
      let hp1 : myNegType (p ≡ _1) := fun q => transport (ltN n') q hlt
      -- every proper divisor x of p is equal to 1
      let hprop : (x : myN) → is_proper_divisor p x → (x ≡ _1) :=
        fun x hx =>
          -- x < p, since x is a proper divisor of p ≠ 0
          let hxp : ltN x p :=
            ltN_of_leqN_neq x p (leqN_of_dividesT x p hp0 (proj2 hx)) (proj1 hx)
          -- by minimality of p, F(n', x) does not hold
          let hnot : myNegType (in_sieve_of_eratosthenes n' x) :=
            fun hs => not_ltN_of_leqN x p (hmin x hs) hxp
          -- every y ≤ n' dividing x divides p, hence equals 1
          let hsieve : (y : myN) → leqN y n' → dividesT y x → (y ≡ _1) :=
            fun y hy hyx => hdiv y hy (dividesT_trans hyx (proj2 hx))
          -- therefore ¬(n' < x), i.e. x ≤ n', and so x = 1
          let hx_le : leqN x n' :=
            leqN_of_not_ltN n' x (fun hlt' => hnot (myProd.mk hlt' hsieve))
          hdiv x hx_le (proj2 hx)
      ⟨p, myProd.mk (is_prime_of_is_prime' p (myProd.mk hp1 hprop))
                    (ltN_trans n n' p (ltN_succ n) hlt)⟩

end chapter8
