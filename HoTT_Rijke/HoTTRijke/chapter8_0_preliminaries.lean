/-
  Chapter 8 — Preliminaries

  Chapter 8 of Rijke's book ("Decidability in elementary number theory") works with
  the natural numbers together with their order relations ≤ and <, divisibility,
  the factorial function and Euclidean division.  All of this was introduced in
  Chapters 6 and 7 of the book, but in this project those notions are spread over
  different natural-number developments:

  * `chapter6.lean` defines the (type-valued) order `leq`, `less_than` on the
    stand-alone naturals `N` of `Inductive_Int.lean`;
  * `chapter7.lean` defines divisibility and the finite types `myFin` on the
    0-based naturals `myN` of `chapter3_naturals_with_zero.lean`, but its
    divisibility relation `divides` is `Prop`-valued (it is truncated with
    `Nonempty`), so the quotient cannot be extracted from a proof of `divides d n`.

  Chapter 8 continues Chapter 7, so we work with the 0-based `myN` throughout and
  collect here the facts from Chapters 5–7 that the sections of Chapter 8 need,
  stated for `myN` with the identity type `MyEq` (`≡`) of `chapter5_eq.lean`:

  * short names for the arithmetic laws of `chapter5_props_naturals_with_zero.lean`;
  * the type-valued order relations `leq` (≤) and `less_than` (<) on `myN`
    (the `myN`-analogues of `leq` and `less_than` from `chapter6.lean`);
  * the proof-relevant divisibility relation `divides d n := Σ k, d * k ≡ n`
    (Definition 7.1.2 of the book), with a bridge to `divides` of `chapter7.lean`;
  * Proposition 7.1.5, Exercise 7.2 (antisymmetry of divisibility),
    Exercise 7.3 (k ∣ n! for 0 < k ≤ n) and Exercise 7.9 (Euclidean division).

  Note: the notation `a ≡ b` of `chapter5_eq.lean` binds more tightly than `+`
  and `*`, so both sides of an identification are always put in parentheses.
-/

import HoTTRijke.chapter6
import HoTTRijke.chapter7

open chapter3_naturals_with_zero
open chapter3_booleans
open chapter5_myeq
open props_naturals_with_zero
open chapter6_Universes

namespace chapter8

/- ###################################################################### -/
/-  Generalities on identifications                                        -/
/- ###################################################################### -/

-- Action on identifications of a function of two variables.
def ap2 {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (p : a ≡ a') (q : b ≡ b') : (f a b) ≡ (f a' b') := by
  cases p
  cases q
  exact MyEq.refl _


/- ###################################################################### -/
/-  Arithmetic of the 0-based natural numbers                              -/
/- ###################################################################### -/


-- Peano's axioms 7 and 8 (Theorems 6.4.1 and 6.4.2) for `myN`.
def succN_inj {m n : myN} (p : myN.succ m ≡ myN.succ n) : m ≡ n := by
  cases p
  exact MyEq.refl _

def succN_neq_zero (n : myN) : myNegType (myN.succ n ≡ myN.zero) :=
  fun p => nomatch p

def zero_neq_succN (n : myN) : myNegType (myN.zero ≡ myN.succ n) :=
  fun p => nomatch p

-- m + n = 0 implies m = 0 and n = 0 (Exercise 6.1 (b) for `myN`).
def addN_eq_zero : (m n : myN) → ((m + n) ≡ myN.zero) → myProd (m ≡ myN.zero) (n ≡ myN.zero)
  | _, myN.zero, p => myProd.mk p (MyEq.refl _)
  | m, myN.succ n, p => Empty.elim (succN_neq_zero (m + n) p)


/- ###################################################################### -/
/-  The order relations ≤ and < on myN (cf. Exercises 6.3 and 6.4)        -/
/- ###################################################################### -/

def leq (m n : myN) : Type :=
  match m, n with
  | myN.zero, _ => Unit
  | myN.succ _, myN.zero => Empty
  | myN.succ m, myN.succ n => leq m n


def leq_refl : (n : myN) → leq n n
  | myN.zero => ()
  | myN.succ n => leq_refl n

def leq_trans : (m n k : myN) → leq m n → leq n k → leq m k
  | myN.zero, _, _, _, _ => ()
  | myN.succ _, myN.zero, _, p, _ => Empty.elim p
  | myN.succ _, myN.succ _, myN.zero, _, q => Empty.elim q
  | myN.succ m, myN.succ n, myN.succ k, p, q => leq_trans m n k p q

def leq_antisymm : (m n : myN) → leq m n → leq n m → (m ≡ n)
  | myN.zero, myN.zero, _, _ => MyEq.refl _
  | myN.zero, myN.succ _, _, q => Empty.elim q
  | myN.succ _, myN.zero, p, _ => Empty.elim p
  | myN.succ m, myN.succ n, p, q => ap myN.succ m n (leq_antisymm m n p q)

def leq_of_eq (m n : myN) (p : m ≡ n) : leq m n := by
  cases p
  exact leq_refl m

-- n ≤ 0 implies n = 0
def leq_zero : (n : myN) → leq n myN.zero → (n ≡ myN.zero)
  | myN.zero, _ => MyEq.refl _
  | myN.succ _, p => Empty.elim p

-- n ≤ n + 1
def leq_succ : (n : myN) → leq n (myN.succ n)
  | myN.zero => ()
  | myN.succ n => leq_succ n

-- k ≤ n + 1 implies (k ≤ n) or (k = n + 1)
def leq_succ_cases : (k n : myN) → leq k (myN.succ n) → Sum (leq k n) (k ≡ myN.succ n)
  | myN.zero, _, _ => Sum.inl ()
  | myN.succ k, myN.zero, p => Sum.inr (ap myN.succ _ _ (leq_zero k p))
  | myN.succ k, myN.succ n, p =>
      match leq_succ_cases k n p with
      | Sum.inl q => Sum.inl q
      | Sum.inr q => Sum.inr (ap myN.succ _ _ q)

-- m ≤ m + k
def leq_add_right : (m k : myN) → leq m (m + k)
  | m, myN.zero => leq_refl m
  | m, myN.succ k =>
      leq_trans m (m + k) (myN.succ (m + k)) (leq_add_right m k) (leq_succ (m + k))

-- k ≤ m + k
def leq_add_left (m k : myN) : leq k (m + k) :=
  transport (fun x => leq k x) (myAdd_commutative k m) (leq_add_right k m)

-- x ≤ x · (k + 1)
def leq_mul_succ_right (x k : myN) : leq x (x * myN.succ k) :=
  match k with
  | myN.zero => leq_refl x
  | myN.succ k' => leq_trans _ _ _ (leq_mul_succ_right x k') (leq_add_left x (x * k'.succ))

def less_than_irrefl : (n : myN) → myNegType (less_than n n)
  | myN.zero, p => p
  | myN.succ n, p => less_than_irrefl n p

-- n < n + 1
def less_than_succ : (n : myN) → less_than n (myN.succ n)
  | myN.zero => ()
  | myN.succ n => less_than_succ n

-- m < n  →  m + 1 ≤ n
def leq_of_less_than : (m n : myN) → less_than m n → leq (myN.succ m) n
  | _, myN.zero, p => Empty.elim p
  | myN.zero, myN.succ _, _ => ()
  | myN.succ m, myN.succ n, p => leq_of_less_than m n p

-- m + 1 ≤ n  →  m < n
def less_than_of_leq : (m n : myN) → leq (myN.succ m) n → less_than m n
  | _, myN.zero, p => Empty.elim p
  | myN.zero, myN.succ _, _ => ()
  | myN.succ m, myN.succ n, p => less_than_of_leq m n p

-- m ≤ n  →  m < n + 1
def less_than_succ_of_leq : (m n : myN) → leq m n → less_than m (myN.succ n)
  | myN.zero, _, _ => ()
  | myN.succ _, myN.zero, p => Empty.elim p
  | myN.succ m, myN.succ n, p => less_than_succ_of_leq m n p

-- m < n + 1  →  m ≤ n
def leq_of_less_than_succ : (m n : myN) → less_than m (myN.succ n) → leq m n
  | myN.zero, _, _ => ()
  | myN.succ _, myN.zero, p => Empty.elim p
  | myN.succ m, myN.succ n, p => leq_of_less_than_succ m n p

def leq_of_less_than' (m n : myN) (p : less_than m n) : leq m n :=
  leq_trans m (myN.succ m) n (leq_succ m) (leq_of_less_than m n p)

def less_than_leq_trans (m n k : myN) (p : less_than m n) (q : leq n k) : less_than m k :=
  less_than_of_leq m k (leq_trans _ _ _ (leq_of_less_than m n p) q)

def leq_less_than_trans (m n k : myN) (p : leq m n) (q : less_than n k) : less_than m k :=
  less_than_of_leq m k (leq_trans (myN.succ m) (myN.succ n) k p (leq_of_less_than n k q))

def less_than_trans (m n k : myN) (p : less_than m n) (q : less_than n k) : less_than m k :=
  less_than_leq_trans m n k p (leq_of_less_than' n k q)

-- ¬(m < n)  →  n ≤ m
def leq_of_not_less_than : (m n : myN) → myNegType (less_than m n) → leq n m
  | _, myN.zero, _ => ()
  | myN.zero, myN.succ _, h => Empty.elim (h ())
  | myN.succ m, myN.succ n, h => leq_of_not_less_than m n h

-- n ≤ m  →  ¬(m < n)
def not_less_than_of_leq (m n : myN) (p : leq n m) : myNegType (less_than m n) :=
  fun q => less_than_irrefl m (less_than_leq_trans m n m q p)

-- m < n  →  m ≠ n
def neq_of_less_than (m n : myN) (p : less_than m n) : myNegType (m ≡ n) := by
  intro q
  cases q
  exact less_than_irrefl m p

-- m ≤ n and m ≠ n  →  m < n
def less_than_of_leq_neq : (m n : myN) → leq m n → myNegType (m ≡ n) → less_than m n
  | myN.zero, myN.zero, _, h => Empty.elim (h (MyEq.refl _))
  | myN.zero, myN.succ _, _, _ => ()
  | myN.succ _, myN.zero, p, _ => Empty.elim p
  | myN.succ m, myN.succ n, p, h => less_than_of_leq_neq m n p (fun q => h (ap myN.succ m n q))

-- n ≠ 0  →  0 < n
def zero_less_than_of_neq_zero : (n : myN) → myNegType (n ≡ myN.zero) → less_than myN.zero n
  | myN.zero, h => Empty.elim (h (MyEq.refl _))
  | myN.succ _, _ => ()

-- r < d  →  (r + 1 < d) or (r + 1 = d)
def less_than_succ_cases : (r d : myN) → less_than r d → Sum (less_than (myN.succ r) d) (myN.succ r ≡ d)
  | _, myN.zero, p => Empty.elim p
  | myN.zero, myN.succ myN.zero, _ => Sum.inr (MyEq.refl _)
  | myN.zero, myN.succ (myN.succ _), _ => Sum.inl ()
  | myN.succ r, myN.succ d, p =>
      match less_than_succ_cases r d p with
      | Sum.inl q => Sum.inl q
      | Sum.inr q => Sum.inr (ap myN.succ _ _ q)


/- ###############################################-/
/-  The distance function (defined in chapter6    -/
/- ############################################## -/

def dist_zero_left (n : myN) : dist myN.zero n ≡ n :=  dist_commutative _ _ • dist_from_zero n

-- Translation invariance: dist(x + k, y + k) = dist(x, y)
def dist_add_both (x y : myN) : (k : myN) → (dist (x + k) (y + k)) ≡ (dist x y)
  | myN.zero => MyEq.refl _
  | myN.succ k => dist_add_both x y k

def dist_add_both_left (x y : myN) (k : myN) : (dist (k + x) (k + y)) ≡ (dist x y) :=
  have h1 : (dist (k + x) (k + y)) ≡ (dist (x + k) (y + k)) := ap2 dist (myAdd_commutative k x) (myAdd_commutative k y)
  h1 • dist_add_both x y k

-- dist(a + b, a) = b
def dist_add_self (a b : myN) : (dist (a + b) a) ≡ b :=
  calc dist (a + b) a ≡ dist (b + a) (myN.zero + a) :=
          ap2 dist (myAdd_commutative a b) (myEq_symm (myAdd_zero_left a))
    _ ≡ dist b myN.zero := dist_add_both b myN.zero a
    _ ≡ b := dist_from_zero b

-- Multiplication distributes over the distance: d · dist(m, n) = dist(d·m, d·n)
def mulN_dist (d : myN) : (m n : myN) → (d * dist m n) ≡ (dist (d * m) (d * n))
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ n => myEq_symm (dist_zero_left (d * myN.succ n))
  | myN.succ m, myN.zero => myEq_symm (dist_from_zero (d * myN.succ m))
  | myN.succ m, myN.succ n =>
      (mulN_dist d m n) • myEq_symm (dist_add_both_left (d * m) (d * n) d)


/- ###################################################################### -/
/-  Divisibility (Definition 7.1.2), proof relevant                        -/
/- ###################################################################### -/

/- `divides d n` is the type Σ (k : ℕ), d · k = n of the book.  Unlike the
   `Prop`-valued `divides` of chapter7.lean it keeps the witness k, which is needed
   to compute with divisibility (e.g. for the Collatz function in Section 8.2). -/
-- abbrev divides (d n : myN) : Type := Σ k : myN, (d * k) ≡ n

-- Every element of `divides d n` gives a proof of `divides d n` of chapter7.lean.
-- def divides_of_divides {d n : myN} (p : divides d n) : divides d n :=
--   Nonempty.intro p

-- n ∣ n
def divides_refl (n : myN) : divides n n := ⟨_1, mult_one_right n⟩

-- n ∣ 0
def divides_zero (n : myN) : divides n myN.zero := ⟨myN.zero, MyEq.refl _⟩

-- 1 ∣ n
def one_divides (n : myN) : divides _1 n := ⟨n, mult_one_left n⟩

-- 0 ∣ n  →  n = 0
def eq_zero_of_zero_divides (n : myN) : divides myN.zero n → (n ≡ myN.zero)
  | ⟨k, p⟩ => (myEq_symm p) • (myMult_zero_left k)

-- a ∣ b and b ∣ c  →  a ∣ c
def divides_trans {a b c : myN} : divides a b → divides b c → divides a c
  | ⟨k, p⟩, ⟨l, q⟩ =>
      ⟨k * l, (myEq_symm (myMult_associative a k l)) • ((ap (fun x => x * l) _ _ p) • q)⟩

-- a ∣ a · b
def divides_mul_right_self (a b : myN) : divides a (a * b) := ⟨b, MyEq.refl _⟩

-- b ∣ a · b
-- def divides_mul_left_self (a b : myN) : divides b (a * b) := ⟨a, mult_commutative b a⟩

-- d ∣ a  →  d ∣ a · b
def divides_mul_right {d a : myN} (b : myN) : divides d a → divides d (a * b)
  | ⟨k, p⟩ => ⟨k * b, (myEq_symm (myMult_associative d k b)) • (ap (fun x => x * b) _ _ p)⟩

-- Proposition 7.1.5: if d divides two of the numbers a, b, a + b, then it divides
-- the third one.

-- d ∣ a and d ∣ b  →  d ∣ a + b
def divides_add {d a b : myN} : divides d a → divides d b → divides d (a + b)
  | ⟨k, p⟩, ⟨l, q⟩ => ⟨k + l, (mult_distributive_left d k l) • (ap2 (fun (x y : myN) => x + y) p q)⟩

-- d ∣ a and d ∣ a + b  →  d ∣ b
def divides_add_cancel_left {d a b : myN} : divides d a → divides d (a + b) → divides d b
  | ⟨k, p⟩, ⟨l, q⟩ => ⟨dist l k, (mulN_dist d l k) • ((ap2 dist q p) • dist_add_self a b)⟩

-- d ∣ b and d ∣ a + b  →  d ∣ a
-- def divides_add_cancel_right {d a b : myN} (p : divides d b) (q : divides d (a + b)) :
--     divides d a :=
--   divides_add_cancel_left p (transport (fun x => divides d x) (myAdd_commutative a b) q)

-- If d ∣ n and n ≠ 0, then d ≤ n.
def leq_of_divides (d n : myN) (h : myNegType (n ≡ myN.zero)) : divides d n → leq d n
  | ⟨myN.zero, p⟩ => Empty.elim (h (myEq_symm p))
  | ⟨myN.succ k, p⟩ => transport (fun x => leq d x) p (leq_mul_succ_right d k)

-- d ∣ 1  →  d = 1
-- def eq_one_of_divides_one : (d : myN) → divides d _1 → (d ≡ _1)
--   | myN.zero, p => Empty.elim (succN_neq_zero _ (eq_zero_of_zero_divides _1 p))
--   | myN.succ myN.zero, _ => MyEq.refl _
--   | myN.succ (myN.succ _), p => Empty.elim (leq_of_divides _ _1 (succN_neq_zero _) p)

-- Exercise 7.2: divisibility is antisymmetric.
def divides_antisymm : (m n : myN) → divides m n → divides n m → (m ≡ n)
  | myN.zero, n, p, _ => myEq_symm (eq_zero_of_zero_divides n p)
  | myN.succ _, myN.zero, _, q => eq_zero_of_zero_divides _ q
  | myN.succ m, myN.succ n, p, q =>
      leq_antisymm _ _ (leq_of_divides _ _ (succN_neq_zero n) p)
                        (leq_of_divides _ _ (succN_neq_zero m) q)


/- ###################################################################### -/
/-  The factorial function (defined in chapter3_naturals_with_zero.lean)   -/
/- ###################################################################### -/

-- def factorial_neq_zero : (n : myN) → myNegType (factorial n ≡ myN.zero)
--   | myN.zero => succN_neq_zero _
--   | myN.succ n => fun p => factorial_neq_zero n (proj2 (addN_eq_zero _ _ p))

-- Exercise 7.3: if 0 < k ≤ n, then k ∣ n!
-- def divides_factorial : (n k : myN) → myNegType (k ≡ myN.zero) → leq k n →
--     divides k (factorial n)
--   | myN.zero, k, hk, p => Empty.elim (hk (leq_zero k p))
--   | myN.succ n, k, hk, p =>
--       match leq_succ_cases k n p with
--       | Sum.inl q => divides_mul_right (myN.succ n) (divides_factorial n k hk q)
--       | Sum.inr q =>
--           transport (fun x => divides x (factorial (myN.succ n))) (myEq_symm q)
--             (divides_mul_left_self (factorial n) (myN.succ n))

-- n ≤ n!
-- def leq_factorial : (n : myN) → leq n (factorial n)
--   | myN.zero => ()
--   | myN.succ n =>
--       leq_of_divides _ _ (factorial_neq_zero _)
--         (divides_factorial (myN.succ n) (myN.succ n) (succN_neq_zero n) (leq_refl _))


/- ###################################################################### -/
/-  Euclidean division (Exercise 7.9)                                      -/
/- ###################################################################### -/

-- For d ≠ 0 and every n there are q and r < d with n = d · q + r.
def euclidean_division (d : myN) (hd : myNegType (d ≡ myN.zero)) :
    (n : myN) → Σ q : myN, Σ r : myN, myProd (less_than r d) (n ≡ ((d * q) + r))
  | myN.zero =>
      ⟨myN.zero, myN.zero, myProd.mk (zero_less_than_of_neq_zero d hd) (MyEq.refl _)⟩
  | myN.succ n =>
      match euclidean_division d hd n with
      | ⟨q, r, myProd.mk hr e⟩ =>
          match less_than_succ_cases r d hr with
          | Sum.inl hr' =>
            have h1 : n.succ ≡ (d * q + r.succ) := ap (fun x : myN => x.succ) _ _ e
            ⟨ q, r.succ, myProd.mk hr' h1⟩
          | Sum.inr r_eq_d =>
            have h1 : n.succ ≡ d * q + r.succ := ap (fun x : myN => x.succ) _ _ e
            have h2 : n.succ ≡ d * q + d := h1 • ap (fun x : myN => d * q + x) _ _ r_eq_d
            have h3 : n.succ ≡ d * q.succ := h2 • myAdd_commutative _ _

            ⟨ q.succ, myN.zero, myProd.mk (zero_less_than_of_neq_zero d hd) h3⟩

/- ###################################################################### -/
/-  Conversion from Lean's `Nat`, for writing concrete examples            -/
/- ###################################################################### -/

def ofNatN : Nat → myN
  | 0 => myN.zero
  | Nat.succ n => myN.succ (ofNatN n)

def toNatN : myN → Nat
  | myN.zero => 0
  | myN.succ n => toNatN n + 1

end chapter8
