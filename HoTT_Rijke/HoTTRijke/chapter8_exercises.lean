/-
  Chapter 8 — Exercises

  Formalized here: 8.1, 8.2, 8.3, 8.4, 8.5, 8.6, 8.7, 8.9, 8.10 and 8.12 (a).

  Not formalized:
  * 8.8  — needs that types with decidable equality are sets (Hedberg's theorem,
           Theorem 12.3.5 of the book) to compare the second components of pairs;
  * 8.11 (Bézout), 8.12 (b)–(c) (prime factorization and its uniqueness),
    8.13 (primes ≡ 3 mod 4), 8.14 (ℤ/p is a field) and 8.15 (cofibonacci) —
           these are substantial projects on their own (8.12 (c) and 8.14 rely on
           Bézout's identity).
-/

import HoTTRijke.chapter8_6_boolean_reflection

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans

namespace chapter8

/- ###################################################################### -/
/-  Exercise 8.1: three open problems stated in type theory                -/
/- ###################################################################### -/

-- (a) Goldbach's conjecture: every even number greater than 2 is a sum of two primes.
abbrev goldbach_conjecture : Type :=
  (n : myN) → ltN _2 n → dividesT _2 n →
    Σ p : myN, Σ q : myN, myProd (is_prime p) (myProd (is_prime q) ((p + q) ≡ n))

-- (b) The twin prime conjecture: there are arbitrarily large primes p such that
--     p + 2 is also prime.
abbrev twin_prime_conjecture : Type :=
  (n : myN) → Σ p : myN, myProd (leqN n p) (myProd (is_prime p) (is_prime (p + _2)))

-- (c) The Collatz conjecture: iterating the Collatz function on any n ≥ 1
--     eventually reaches 1.
def iterate {A : Type} (f : A → A) : myN → A → A
  | myN.zero, a => a
  | myN.succ k, a => f (iterate f k a)

abbrev collatz_conjecture : Type :=
  (n : myN) → Σ k : myN, (iterate collatz k (myN.succ n)) ≡ _1

-- Instances can be checked by computation:
def is_prime_3 : is_prime _3 := reflect (is_decidable_is_prime _3) (MyEq.refl _)

-- 10 = 3 + 7
example : Σ p : myN, Σ q : myN, myProd (is_prime p) (myProd (is_prime q) ((p + q) ≡ _10)) :=
  ⟨_3, _7, myProd.mk is_prime_3 (myProd.mk is_prime_7 (MyEq.refl _))⟩

-- 6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1
example : Σ k : myN, (iterate collatz k _6) ≡ _1 := ⟨_8, MyEq.refl _⟩


/- ###################################################################### -/
/-  Exercise 8.2                                                           -/
/- ###################################################################### -/

def is_decidable_of_is_decidable_is_decidable {A : Type} :
    is_decidable (is_decidable A) → is_decidable A
  | Sum.inl d => d
  -- ¬(A + ¬A) is contradictory: it implies ¬A, and hence A + ¬A.
  | Sum.inr f => Empty.elim (f (Sum.inr (fun a => f (Sum.inl a))))


/- ###################################################################### -/
/-  Exercise 8.3                                                           -/
/- ###################################################################### -/

-- For a decidable family P over Fin k:  ¬(Π (x : Fin k), P(x)) → Σ (x : Fin k), ¬P(x)
def exists_not_of_not_forall_Fin : (k : myN) → (P : myFin k → Type) →
    is_decidable_family P → myNegType ((x : myFin k) → P x) → Σ x : myFin k, myNegType (P x)
  | myN.zero, _, _, h => Empty.elim (h (fun x => Empty.elim x))
  | myN.succ k, P, d, h =>
      match d (Sum.inr ()) with
      | Sum.inr np => ⟨Sum.inr (), np⟩
      | Sum.inl p =>
          match exists_not_of_not_forall_Fin k (fun x => P (Sum.inl x)) (fun x => d (Sum.inl x))
                  (fun f => h (fun x =>
                    match x with
                    | Sum.inl x => f x
                    | Sum.inr () => p)) with
          | ⟨x, nx⟩ => ⟨Sum.inl x, nx⟩


/- ###################################################################### -/
/-  Exercise 8.4: the prime function and the prime-counting function      -/
/- ###################################################################### -/

-- The least prime p with m < p exists by Theorem 8.5.6 and the well-ordering principle.
def next_prime (m : myN) : minimal_element (fun p => myProd (ltN m p) (is_prime p)) :=
  well_ordering_principle (fun p => myProd (ltN m p) (is_prime p))
    (fun p => is_decidable_prod (is_decidable_ltN m p) (is_decidable_is_prime p))
    ⟨(infinitude_of_primes m).1,
      myProd.mk (proj2 (infinitude_of_primes m).2) (proj1 (infinitude_of_primes m).2)⟩

-- (a) prime(n) is the n-th prime, counting from prime(0) = 2.
def prime_fn : myN → myN
  | myN.zero => (next_prime myN.zero).1
  | myN.succ n => (next_prime (prime_fn n)).1

def is_prime_prime_fn : (n : myN) → is_prime (prime_fn n)
  | myN.zero => proj2 (proj1 (next_prime myN.zero).2)
  | myN.succ n => proj2 (proj1 (next_prime (prime_fn n)).2)

-- prime(n) < prime(n + 1) ...
def prime_fn_ltN_succ (n : myN) : ltN (prime_fn n) (prime_fn (myN.succ n)) :=
  proj1 (proj1 (next_prime (prime_fn n)).2)

-- ... and there are no primes in between.
def prime_fn_succ_minimal (n p : myN) (h : ltN (prime_fn n) p) (hp : is_prime p) :
    leqN (prime_fn (myN.succ n)) p :=
  proj2 (next_prime (prime_fn n)).2 p (myProd.mk h hp)

example : (prime_fn _0) ≡ _2 := MyEq.refl _
example : (prime_fn _2) ≡ _5 := MyEq.refl _

-- (b) π(n) is the number of primes p ≤ n.
def prime_counting : myN → myN
  | myN.zero => myN.zero
  | myN.succ n =>
      match is_decidable_is_prime (myN.succ n) with
      | Sum.inl _ => myN.succ (prime_counting n)
      | Sum.inr _ => prime_counting n

-- The primes ≤ 10 are 2, 3, 5 and 7.
example : (prime_counting _10) ≡ _4 := MyEq.refl _


/- ###################################################################### -/
/-  Exercise 8.5                                                           -/
/- ###################################################################### -/

def not_is_prime_zero : myNegType (is_prime myN.zero) :=
  fun H => two_neq_one (proj2 (is_prime'_of_is_prime _ H) _2
                          (myProd.mk (succN_neq_zero _1) (dividesT_zero _2)))

def two_leqN_of_neq (n : myN) : myNegType (n ≡ myN.zero) → myNegType (n ≡ _1) → leqN _2 n :=
  match n with
  | myN.zero => fun h0 _ => Empty.elim (h0 (MyEq.refl _))
  | myN.succ myN.zero => fun _ h1 => Empty.elim (h1 (MyEq.refl _))
  | myN.succ (myN.succ _) => fun _ _ => ()

-- is-prime(n) ↔ (2 ≤ n) × Π (x : ℕ), (x ∣ n) → (x = 1) + (x = n)
def is_prime_iff_divisors (n : myN) :
    myEquiv (is_prime n)
      (myProd (leqN _2 n) ((x : myN) → dividesT x n → Sum (x ≡ _1) (x ≡ n))) :=
  myProd.mk
    (fun H =>
      let H' := is_prime'_of_is_prime n H
      let h0 : myNegType (n ≡ myN.zero) := fun e => not_is_prime_zero (transport is_prime e H)
      myProd.mk (two_leqN_of_neq n h0 (proj1 H'))
        (fun x hx =>
          match has_decidable_eq_myN x n with
          | Sum.inl e => Sum.inr e
          | Sum.inr ne => Sum.inl (proj2 H' x (myProd.mk ne hx))))
    (fun H =>
      is_prime_of_is_prime' n
        (myProd.mk
          (fun e => transport (fun y => leqN _2 y) e (proj1 H))
          (fun x hx =>
            match proj2 H x (proj2 hx) with
            | Sum.inl e => e
            | Sum.inr e => Empty.elim (proj1 hx e))))


/- ###################################################################### -/
/-  Exercise 8.6: decidable equality of products                          -/
/- ###################################################################### -/

-- The identity type of A × B.
def eq_myProd_iff {A B : Type} (a a' : A) (b b' : B) :
    myEquiv (myProd.mk a b ≡ myProd.mk a' b') (myProd (a ≡ a') (b ≡ b')) :=
  myProd.mk
    (fun p => myProd.mk (ap proj1 _ _ p) (ap proj2 _ _ p))
    (fun q => ap2 myProd.mk (proj1 q) (proj2 q))

-- (i) (B → has-decidable-eq(A)) × (A → has-decidable-eq(B))  ↔  (ii) has-decidable-eq(A × B)
def has_decidable_eq_prod_iff (A B : Type) :
    myEquiv (myProd (B → has_decidable_eq A) (A → has_decidable_eq B))
            (has_decidable_eq (myProd A B)) :=
  myProd.mk
    (fun H x y =>
      match x, y with
      | myProd.mk a b, myProd.mk a' b' =>
          is_decidable_of_iff
            (myProd.mk (proj2 (eq_myProd_iff a a' b b')) (proj1 (eq_myProd_iff a a' b b')))
            (is_decidable_prod (proj1 H b a a') (proj2 H a b b')))
    (fun d => myProd.mk
      (fun b a a' =>
        is_decidable_of_iff
          (myProd.mk (fun p => proj1 (proj1 (eq_myProd_iff a a' b b) p))
                     (fun q => proj2 (eq_myProd_iff a a' b b) (myProd.mk q (MyEq.refl b))))
          (d (myProd.mk a b) (myProd.mk a' b)))
      (fun a b b' =>
        is_decidable_of_iff
          (myProd.mk (fun p => proj2 (proj1 (eq_myProd_iff a a b b') p))
                     (fun q => proj2 (eq_myProd_iff a a b b') (myProd.mk (MyEq.refl a) q)))
          (d (myProd.mk a b) (myProd.mk a b'))))

-- If A and B have decidable equality, then so does A × B.
def has_decidable_eq_prod {A B : Type} (dA : has_decidable_eq A) (dB : has_decidable_eq B) :
    has_decidable_eq (myProd A B) :=
  proj1 (has_decidable_eq_prod_iff A B) (myProd.mk (fun _ => dA) (fun _ => dB))


/- ###################################################################### -/
/-  Exercise 8.7: decidable equality of coproducts                        -/
/- ###################################################################### -/

def Eq_copr {A B : Type} : A ⊕ B → A ⊕ B → Type
  | Sum.inl a, Sum.inl a' => a ≡ a'
  | Sum.inl _, Sum.inr _ => Empty
  | Sum.inr _, Sum.inl _ => Empty
  | Sum.inr b, Sum.inr b' => b ≡ b'

def Eq_copr_refl {A B : Type} : (x : A ⊕ B) → Eq_copr x x
  | Sum.inl a => MyEq.refl a
  | Sum.inr b => MyEq.refl b

def eq_of_Eq_copr {A B : Type} : (x y : A ⊕ B) → Eq_copr x y → (x ≡ y)
  | Sum.inl a, Sum.inl a', p => ap Sum.inl a a' p
  | Sum.inl _, Sum.inr _, e => Empty.elim e
  | Sum.inr _, Sum.inl _, e => Empty.elim e
  | Sum.inr b, Sum.inr b', p => ap Sum.inr b b' p

-- (a) (x = y) ↔ Eq-copr(x, y)
def eq_iff_Eq_copr {A B : Type} (x y : A ⊕ B) : myEquiv (x ≡ y) (Eq_copr x y) :=
  myProd.mk (fun p => transport (Eq_copr x) p (Eq_copr_refl x)) (eq_of_Eq_copr x y)

def is_decidable_Eq_copr {A B : Type} (dA : has_decidable_eq A) (dB : has_decidable_eq B) :
    (x y : A ⊕ B) → is_decidable (Eq_copr x y)
  | Sum.inl a, Sum.inl a' => dA a a'
  | Sum.inl _, Sum.inr _ => is_decidable_empty
  | Sum.inr _, Sum.inl _ => is_decidable_empty
  | Sum.inr b, Sum.inr b' => dB b b'

-- (b) A and B have decidable equality if and only if A + B has decidable equality.
def has_decidable_eq_sum_iff (A B : Type) :
    myEquiv (myProd (has_decidable_eq A) (has_decidable_eq B)) (has_decidable_eq (A ⊕ B)) :=
  myProd.mk
    (fun H x y =>
      is_decidable_of_iff (myProd.mk (eq_of_Eq_copr x y) (proj1 (eq_iff_Eq_copr x y)))
        (is_decidable_Eq_copr (proj1 H) (proj2 H) x y))
    (fun d => myProd.mk
      (fun a a' => is_decidable_of_iff (eq_iff_Eq_copr (Sum.inl a) (Sum.inl a'))
                     (d (Sum.inl a) (Sum.inl a')))
      (fun b b' => is_decidable_of_iff (eq_iff_Eq_copr (Sum.inr b) (Sum.inr b'))
                     (d (Sum.inr b) (Sum.inr b'))))

def has_decidable_eq_sum {A B : Type} (dA : has_decidable_eq A) (dB : has_decidable_eq B) :
    has_decidable_eq (A ⊕ B) :=
  proj1 (has_decidable_eq_sum_iff A B) (myProd.mk dA dB)

/- Conclusion: ℤ has decidable equality.  In chapter3.lean the integers are
   `myZ := myN ⊕ (Unit ⊕ myN)`, built on the 1-based naturals of that file. -/

def has_decidable_eq_unit : has_decidable_eq Unit :=
  fun _ _ => Sum.inl (MyEq.refl _)

def has_decidable_eq_myN_one_based : has_decidable_eq chapter3_naturals.myN
  | chapter3_naturals.myN.one, chapter3_naturals.myN.one => Sum.inl (MyEq.refl _)
  | chapter3_naturals.myN.one, chapter3_naturals.myN.succ _ => Sum.inr (fun p => nomatch p)
  | chapter3_naturals.myN.succ _, chapter3_naturals.myN.one => Sum.inr (fun p => nomatch p)
  | chapter3_naturals.myN.succ m, chapter3_naturals.myN.succ n =>
      match has_decidable_eq_myN_one_based m n with
      | Sum.inl p => Sum.inl (ap chapter3_naturals.myN.succ m n p)
      | Sum.inr f => Sum.inr (fun p => f (by cases p; exact MyEq.refl _))

def has_decidable_eq_myZ : has_decidable_eq chapter3_integers.myZ :=
  has_decidable_eq_sum has_decidable_eq_myN_one_based
    (has_decidable_eq_sum has_decidable_eq_unit has_decidable_eq_myN_one_based)


/- ###################################################################### -/
/-  Exercise 8.9: families over the standard finite types                 -/
/- ###################################################################### -/

-- (a) If each P(x) is decidable, then Π (x : Fin k), P(x) is decidable.
def is_decidable_pi_Fin : (k : myN) → (P : myFin k → Type) → is_decidable_family P →
    is_decidable ((x : myFin k) → P x)
  | myN.zero, _, _ => Sum.inl (fun x => Empty.elim x)
  | myN.succ k, P, d =>
      match is_decidable_pi_Fin k (fun x => P (Sum.inl x)) (fun x => d (Sum.inl x)),
            d (Sum.inr ()) with
      | Sum.inl f, Sum.inl p =>
          Sum.inl (fun x =>
            match x with
            | Sum.inl x => f x
            | Sum.inr () => p)
      | Sum.inl _, Sum.inr np => Sum.inr (fun g => np (g (Sum.inr ())))
      | Sum.inr nf, _ => Sum.inr (fun g => nf (fun x => g (Sum.inl x)))

/- (b) needs function extensionality, which the book introduces only in Chapter 13.
   We obtain it for `MyEq` from Lean's `funext` (as in chapter2.lean). -/

def eq_of_myEq {α : Type} {a b : α} (p : a ≡ b) : a = b := by
  cases p
  rfl

-- `Eq` eliminates into every universe, so this conversion needs no axioms.
def myEq_of_eq {α : Type} {a b : α} (h : a = b) : a ≡ b := h ▸ MyEq.refl a

def myFunext {A : Type} {B : A → Type} {f g : (x : A) → B x}
    (h : (x : A) → (f x) ≡ (g x)) : f ≡ g :=
  myEq_of_eq (funext (fun x => eq_of_myEq (h x)))

def myHapply {A : Type} {B : A → Type} {f g : (x : A) → B x} (p : f ≡ g) (x : A) :
    (f x) ≡ (g x) := by
  cases p
  exact MyEq.refl _

-- (b) If each B(x) has decidable equality, then so does Π (x : Fin k), B(x).
def has_decidable_eq_pi_Fin (k : myN) (B : myFin k → Type)
    (d : (x : myFin k) → has_decidable_eq (B x)) : has_decidable_eq ((x : myFin k) → B x) :=
  fun f g =>
    is_decidable_of_iff (myProd.mk myFunext myHapply)
      (is_decidable_pi_Fin k (fun x => (f x) ≡ (g x)) (fun x => d x (f x) (g x)))


/- ###################################################################### -/
/-  Exercise 8.10: bounded decidable families                             -/
/- ###################################################################### -/

-- (a) If P is decidable and has an upper bound, then Σ (x : ℕ), P(x) is decidable.
def is_decidable_sigma_of_upper_bound (P : myN → Type) (d : is_decidable_family P)
    (m : myN) (ub : is_upper_bound P m) : is_decidable (Σ x : myN, P x) :=
  is_decidable_of_iff
    (myProd.mk (fun ⟨x, myProd.mk _ p⟩ => ⟨x, p⟩) (fun ⟨x, p⟩ => ⟨x, myProd.mk (ub x p) p⟩))
    (is_decidable_bounded_sigma P d m)

abbrev maximal_element (P : myN → Type) : Type :=
  Σ m : myN, myProd (P m) (is_upper_bound P m)

/- (b) If P is decidable, has an upper bound m and is inhabited, then P has a maximal
   element: the least upper bound of P, obtained with the well-ordering principle. -/
def maximal_element_of_upper_bound (P : myN → Type) (d : is_decidable_family P)
    (m : myN) (ub : is_upper_bound P m) (x0 : Σ x : myN, P x) : maximal_element P :=
  -- "y is an upper bound of P" is decidable by Corollary 8.2.5
  let dQ : is_decidable_family (is_upper_bound P) := fun y =>
    is_decidable_pi_implication P (fun x => leqN x y) d (fun x => is_decidable_leqN x y) m ub
  match well_ordering_principle (is_upper_bound P) dQ ⟨m, ub⟩ with
  | ⟨y, myProd.mk uby lby⟩ =>
      match d y with
      | Sum.inl py => ⟨y, myProd.mk py uby⟩
      | Sum.inr npy =>
          -- if ¬P(y), then y ≠ 0 (as x0 ≤ y) and y - 1 would be a smaller upper bound
          Empty.elim (
            match y, uby, lby, npy with
            | myN.zero, uby, _, npy =>
                npy (transport P (leqN_zero x0.1 (uby x0.1 x0.2)) x0.2)
            | myN.succ y, uby, lby, npy =>
                not_leqN_succ_self y (lby y (fun x px =>
                  match leqN_succ_cases x y (uby x px) with
                  | Sum.inl h => h
                  | Sum.inr e => Empty.elim (npy (transport P e px)))))

-- (c) A second construction of the gcd: the largest common divisor of a and b
--     (and 0 if a = b = 0).

abbrev is_common_divisor (a b x : myN) : Type := myProd (dividesT x a) (dividesT x b)

def is_decidable_is_common_divisor (a b : myN) : is_decidable_family (is_common_divisor a b) :=
  fun x => is_decidable_prod (is_decidable_dividesT x a) (is_decidable_dividesT x b)

-- If a + b ≠ 0, the common divisors of a and b are bounded by a + b.
def is_upper_bound_common_divisor (a b : myN) (h : myNegType ((a + b) ≡ myN.zero)) :
    is_upper_bound (is_common_divisor a b) (a + b) :=
  fun x hx => leqN_of_dividesT x (a + b) h (dividesT_add (proj1 hx) (proj2 hx))

-- If a + b ≠ 0, the largest common divisor exists by part (b) (1 is a common divisor).
def max_common_divisor (a b : myN) (h : myNegType ((a + b) ≡ myN.zero)) :
    maximal_element (is_common_divisor a b) :=
  maximal_element_of_upper_bound (is_common_divisor a b) (is_decidable_is_common_divisor a b)
    (a + b) (is_upper_bound_common_divisor a b h)
    ⟨_1, myProd.mk (one_dividesT a) (one_dividesT b)⟩

def gcd2_h (a b : myN) : is_decidable ((a + b) ≡ myN.zero) → myN
  | Sum.inl _ => myN.zero
  | Sum.inr h => (max_common_divisor a b h).1

def gcd2 (a b : myN) : myN := gcd2_h a b (has_decidable_eq_myN (a + b) myN.zero)

-- If a = b = 0, then 0 is a gcd of a and b.
def is_gcd_zero_of_add_eq_zero (a b : myN) (h : (a + b) ≡ myN.zero) : is_gcd a b myN.zero :=
  fun x => myProd.mk
    (fun _ => dividesT_zero x)
    (fun _ => myProd.mk
      (transport (fun y => dividesT x y) (myEq_symm (proj1 (addN_eq_zero a b h))) (dividesT_zero x))
      (transport (fun y => dividesT x y) (myEq_symm (proj2 (addN_eq_zero a b h))) (dividesT_zero x)))

/- gcd2(a, b) satisfies the specification of Definition 8.4.1: it coincides with
   gcd(a, b) of Definition 8.4.6, because each of the two divides the other. -/
def is_gcd_gcd2_h (a b : myN) : (e : is_decidable ((a + b) ≡ myN.zero)) → is_gcd a b (gcd2_h a b e)
  | Sum.inl h => is_gcd_zero_of_add_eq_zero a b h
  | Sum.inr h =>
      let M := (max_common_divisor a b h).1
      let hM : is_common_divisor a b M := proj1 (max_common_divisor a b h).2
      let ubM : is_upper_bound (is_common_divisor a b) M := proj2 (max_common_divisor a b h).2
      let hg : myNegType (gcdN a b ≡ myN.zero) := fun p => h (proj1 (gcdN_eq_zero_iff a b) p)
      -- gcd(a, b) is a common divisor, so gcd(a, b) ≤ M
      let h1 : leqN (gcdN a b) M :=
        ubM (gcdN a b) (myProd.mk (gcdN_dividesT_left a b) (gcdN_dividesT_right a b))
      -- M is a common divisor, so M ∣ gcd(a, b) and hence M ≤ gcd(a, b)
      let h2 : leqN M (gcdN a b) :=
        leqN_of_dividesT M (gcdN a b) hg (proj1 (is_gcd_gcdN a b M) hM)
      transport (is_gcd a b) (leqN_antisymm _ _ h1 h2) (is_gcd_gcdN a b)

def is_gcd_gcd2 (a b : myN) : is_gcd a b (gcd2 a b) :=
  is_gcd_gcd2_h a b (has_decidable_eq_myN (a + b) myN.zero)

example : (gcd2 _4 _6) ≡ _2 := MyEq.refl _


/- ###################################################################### -/
/-  Exercise 8.12 (a): every n ≥ 2 has a prime factor                      -/
/- ###################################################################### -/

-- The least d ≥ 2 dividing n is prime.
def prime_factor (n : myN) (h : leqN _2 n) : Σ p : myN, myProd (is_prime p) (dividesT p n) :=
  match well_ordering_principle (fun d => myProd (leqN _2 d) (dividesT d n))
          (fun d => is_decidable_prod (is_decidable_leqN _2 d) (is_decidable_dividesT d n))
          ⟨n, myProd.mk h (dividesT_refl n)⟩ with
  | ⟨p, myProd.mk (myProd.mk h2 hpn) hmin⟩ =>
      let hp0 : myNegType (p ≡ myN.zero) := fun e => transport (fun y => leqN _2 y) e h2
      let hp1 : myNegType (p ≡ _1) := fun e => transport (fun y => leqN _2 y) e h2
      let hprop : (x : myN) → is_proper_divisor p x → (x ≡ _1) := fun x hx =>
        match has_decidable_eq_myN x _1 with
        | Sum.inl e => e
        | Sum.inr ne1 =>
            -- x ≠ 0, since 0 ∤ p
            let hx0 : myNegType (x ≡ myN.zero) := fun e =>
              hp0 (eq_zero_of_zero_dividesT p (transport (fun y => dividesT y p) e (proj2 hx)))
            -- x < p, but x ≥ 2 divides n, so p ≤ x by minimality
            let hxp : ltN x p :=
              ltN_of_leqN_neq x p (leqN_of_dividesT x p hp0 (proj2 hx)) (proj1 hx)
            Empty.elim (not_ltN_of_leqN x p
              (hmin x (myProd.mk (two_leqN_of_neq x hx0 ne1) (dividesT_trans (proj2 hx) hpn)))
              hxp)
      ⟨p, myProd.mk (is_prime_of_is_prime' p (myProd.mk hp1 hprop)) hpn⟩

example : (prime_factor (ofNatN 91) ()).1 ≡ _7 := MyEq.refl _

end chapter8
