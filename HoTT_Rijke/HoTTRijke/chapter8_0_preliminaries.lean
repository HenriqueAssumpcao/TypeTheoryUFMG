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
  * the type-valued order relations `leqN` (≤) and `ltN` (<) on `myN`
    (the `myN`-analogues of `leq` and `less_than` from `chapter6.lean`);
  * the proof-relevant divisibility relation `dividesT d n := Σ k, d * k ≡ n`
    (Definition 7.1.2 of the book), with a bridge to `divides` of `chapter7.lean`;
  * Proposition 7.1.5, Exercise 7.2 (antisymmetry of divisibility),
    Exercise 7.3 (k ∣ n! for 0 < k ≤ n) and Exercise 7.9 (Euclidean division).

  Note: the notation `a ≡ b` of `chapter5_eq.lean` binds more tightly than `+`
  and `*`, so both sides of an identification are always put in parentheses.
-/

import HoTTRijke.chapter7

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans
import chapter5_props_naturals_with_zero

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

/- Short names for the laws proved in `chapter5_props_naturals_with_zero.lean`.
   (The root namespace contains homonymous lemmas about `Inductive_Int.N`,
   so we give the `myN`-versions their own names here.) -/

def addN_zero_left (a : myN) : (myN.zero + a) ≡ a :=
  props_naturals_with_zero.myAdd_zero_left_N a

def addN_succ_left (a b : myN) : (myN.succ a + b) ≡ myN.succ (a + b) :=
  props_naturals_with_zero.left_successor_law_add a b

def addN_comm (a b : myN) : (a + b) ≡ (b + a) :=
  props_naturals_with_zero.add_commutative a b

def addN_assoc (a b c : myN) : ((a + b) + c) ≡ (a + (b + c)) :=
  props_naturals_with_zero.add_associative a b c

def mulN_zero_left (a : myN) : (myN.zero * a) ≡ myN.zero :=
  props_naturals_with_zero.mult_zero_left a

def mulN_one_left (a : myN) : (_1 * a) ≡ a :=
  props_naturals_with_zero.mult_one_left a

def mulN_one_right (a : myN) : (a * _1) ≡ a :=
  props_naturals_with_zero.mult_one_right a

def mulN_comm (a b : myN) : (a * b) ≡ (b * a) :=
  props_naturals_with_zero.mult_commutative a b

def mulN_assoc (a b c : myN) : ((a * b) * c) ≡ (a * (b * c)) :=
  props_naturals_with_zero.mult_associative a b c

def mulN_distrib_left (a b c : myN) : (a * (b + c)) ≡ ((a * b) + (a * c)) :=
  props_naturals_with_zero.mult_distributive_left a b c


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

-- m ≤ n
def leqN : myN → myN → Type
  | myN.zero, _ => Unit
  | myN.succ _, myN.zero => Empty
  | myN.succ m, myN.succ n => leqN m n

-- m < n   (we match on n first, so that `ltN m 0` reduces to `Empty` for every m)
def ltN (m n : myN) : Type :=
  match n, m with
  | myN.zero, _ => Empty
  | myN.succ _, myN.zero => Unit
  | myN.succ n, myN.succ m => ltN m n
termination_by structural n


def leqN_refl : (n : myN) → leqN n n
  | myN.zero => ()
  | myN.succ n => leqN_refl n

def leqN_trans : (m n k : myN) → leqN m n → leqN n k → leqN m k
  | myN.zero, _, _, _, _ => ()
  | myN.succ _, myN.zero, _, p, _ => Empty.elim p
  | myN.succ _, myN.succ _, myN.zero, _, q => Empty.elim q
  | myN.succ m, myN.succ n, myN.succ k, p, q => leqN_trans m n k p q

def leqN_antisymm : (m n : myN) → leqN m n → leqN n m → (m ≡ n)
  | myN.zero, myN.zero, _, _ => MyEq.refl _
  | myN.zero, myN.succ _, _, q => Empty.elim q
  | myN.succ _, myN.zero, p, _ => Empty.elim p
  | myN.succ m, myN.succ n, p, q => ap myN.succ m n (leqN_antisymm m n p q)

def leqN_of_eq (m n : myN) (p : m ≡ n) : leqN m n := by
  cases p
  exact leqN_refl m

-- n ≤ 0 implies n = 0
def leqN_zero : (n : myN) → leqN n myN.zero → (n ≡ myN.zero)
  | myN.zero, _ => MyEq.refl _
  | myN.succ _, p => Empty.elim p

-- n ≤ n + 1
def leqN_succ : (n : myN) → leqN n (myN.succ n)
  | myN.zero => ()
  | myN.succ n => leqN_succ n

-- k ≤ n + 1 implies (k ≤ n) or (k = n + 1)
def leqN_succ_cases : (k n : myN) → leqN k (myN.succ n) → Sum (leqN k n) (k ≡ myN.succ n)
  | myN.zero, _, _ => Sum.inl ()
  | myN.succ k, myN.zero, p => Sum.inr (ap myN.succ _ _ (leqN_zero k p))
  | myN.succ k, myN.succ n, p =>
      match leqN_succ_cases k n p with
      | Sum.inl q => Sum.inl q
      | Sum.inr q => Sum.inr (ap myN.succ _ _ q)

-- m ≤ m + k
def leqN_add_right : (m k : myN) → leqN m (m + k)
  | m, myN.zero => leqN_refl m
  | m, myN.succ k =>
      leqN_trans m (m + k) (myN.succ (m + k)) (leqN_add_right m k) (leqN_succ (m + k))

-- k ≤ m + k
def leqN_add_left (m k : myN) : leqN k (m + k) :=
  transport (fun x => leqN k x) (addN_comm k m) (leqN_add_right k m)

-- x ≤ x · (k + 1)
def leqN_mul_succ_right (x k : myN) : leqN x (x * myN.succ k) :=
  leqN_add_left (x * k) x


def ltN_irrefl : (n : myN) → myNegType (ltN n n)
  | myN.zero, p => p
  | myN.succ n, p => ltN_irrefl n p

-- n < n + 1
def ltN_succ : (n : myN) → ltN n (myN.succ n)
  | myN.zero => ()
  | myN.succ n => ltN_succ n

-- m < n  →  m + 1 ≤ n
def leqN_of_ltN : (m n : myN) → ltN m n → leqN (myN.succ m) n
  | _, myN.zero, p => Empty.elim p
  | myN.zero, myN.succ _, _ => ()
  | myN.succ m, myN.succ n, p => leqN_of_ltN m n p

-- m + 1 ≤ n  →  m < n
def ltN_of_leqN : (m n : myN) → leqN (myN.succ m) n → ltN m n
  | _, myN.zero, p => Empty.elim p
  | myN.zero, myN.succ _, _ => ()
  | myN.succ m, myN.succ n, p => ltN_of_leqN m n p

-- m ≤ n  →  m < n + 1
def ltN_succ_of_leqN : (m n : myN) → leqN m n → ltN m (myN.succ n)
  | myN.zero, _, _ => ()
  | myN.succ _, myN.zero, p => Empty.elim p
  | myN.succ m, myN.succ n, p => ltN_succ_of_leqN m n p

-- m < n + 1  →  m ≤ n
def leqN_of_ltN_succ : (m n : myN) → ltN m (myN.succ n) → leqN m n
  | myN.zero, _, _ => ()
  | myN.succ _, myN.zero, p => Empty.elim p
  | myN.succ m, myN.succ n, p => leqN_of_ltN_succ m n p

def leqN_of_ltN' (m n : myN) (p : ltN m n) : leqN m n :=
  leqN_trans m (myN.succ m) n (leqN_succ m) (leqN_of_ltN m n p)

def ltN_leqN_trans (m n k : myN) (p : ltN m n) (q : leqN n k) : ltN m k :=
  ltN_of_leqN m k (leqN_trans _ _ _ (leqN_of_ltN m n p) q)

def leqN_ltN_trans (m n k : myN) (p : leqN m n) (q : ltN n k) : ltN m k :=
  ltN_of_leqN m k (leqN_trans (myN.succ m) (myN.succ n) k p (leqN_of_ltN n k q))

def ltN_trans (m n k : myN) (p : ltN m n) (q : ltN n k) : ltN m k :=
  ltN_leqN_trans m n k p (leqN_of_ltN' n k q)

-- ¬(m < n)  →  n ≤ m
def leqN_of_not_ltN : (m n : myN) → myNegType (ltN m n) → leqN n m
  | _, myN.zero, _ => ()
  | myN.zero, myN.succ _, h => Empty.elim (h ())
  | myN.succ m, myN.succ n, h => leqN_of_not_ltN m n h

-- n ≤ m  →  ¬(m < n)
def not_ltN_of_leqN (m n : myN) (p : leqN n m) : myNegType (ltN m n) :=
  fun q => ltN_irrefl m (ltN_leqN_trans m n m q p)

-- m < n  →  m ≠ n
def neq_of_ltN (m n : myN) (p : ltN m n) : myNegType (m ≡ n) := by
  intro q
  cases q
  exact ltN_irrefl m p

-- m ≤ n and m ≠ n  →  m < n
def ltN_of_leqN_neq : (m n : myN) → leqN m n → myNegType (m ≡ n) → ltN m n
  | myN.zero, myN.zero, _, h => Empty.elim (h (MyEq.refl _))
  | myN.zero, myN.succ _, _, _ => ()
  | myN.succ _, myN.zero, p, _ => Empty.elim p
  | myN.succ m, myN.succ n, p, h => ltN_of_leqN_neq m n p (fun q => h (ap myN.succ m n q))

-- n ≠ 0  →  0 < n
def zero_ltN_of_neq_zero : (n : myN) → myNegType (n ≡ myN.zero) → ltN myN.zero n
  | myN.zero, h => Empty.elim (h (MyEq.refl _))
  | myN.succ _, _ => ()

-- r < d  →  (r + 1 < d) or (r + 1 = d)
def ltN_succ_cases : (r d : myN) → ltN r d → Sum (ltN (myN.succ r) d) (myN.succ r ≡ d)
  | _, myN.zero, p => Empty.elim p
  | myN.zero, myN.succ myN.zero, _ => Sum.inr (MyEq.refl _)
  | myN.zero, myN.succ (myN.succ _), _ => Sum.inl ()
  | myN.succ r, myN.succ d, p =>
      match ltN_succ_cases r d p with
      | Sum.inl q => Sum.inl q
      | Sum.inr q => Sum.inr (ap myN.succ _ _ q)


/- ###################################################################### -/
/-  The distance function (defined in chapter3_naturals_with_zero.lean)    -/
/- ###################################################################### -/

def dist_zero_left : (n : myN) → (dist myN.zero n) ≡ n
  | myN.zero => MyEq.refl _
  | myN.succ _ => MyEq.refl _

-- Translation invariance: dist(x + k, y + k) = dist(x, y)
def dist_add_both (x y : myN) : (k : myN) → (dist (x + k) (y + k)) ≡ (dist x y)
  | myN.zero => MyEq.refl _
  | myN.succ k => dist_add_both x y k

-- dist(a + b, a) = b
def dist_add_self (a b : myN) : (dist (a + b) a) ≡ b :=
  calc dist (a + b) a ≡ dist (b + a) (myN.zero + a) :=
          ap2 dist (addN_comm a b) (myEq_symm (addN_zero_left a))
    _ ≡ dist b myN.zero := dist_add_both b myN.zero a
    _ ≡ b := props_naturals_with_zero.dist_from_zero b

-- Multiplication distributes over the distance: d · dist(m, n) = dist(d·m, d·n)
def mulN_dist (d : myN) : (m n : myN) → (d * dist m n) ≡ (dist (d * m) (d * n))
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ n => myEq_symm (dist_zero_left (d * myN.succ n))
  | myN.succ m, myN.zero => myEq_symm (props_naturals_with_zero.dist_from_zero (d * myN.succ m))
  | myN.succ m, myN.succ n =>
      (mulN_dist d m n) • myEq_symm (dist_add_both (d * m) (d * n) d)


/- ###################################################################### -/
/-  Divisibility (Definition 7.1.2), proof relevant                        -/
/- ###################################################################### -/

/- `dividesT d n` is the type Σ (k : ℕ), d · k = n of the book.  Unlike the
   `Prop`-valued `divides` of chapter7.lean it keeps the witness k, which is needed
   to compute with divisibility (e.g. for the Collatz function in Section 8.2). -/
abbrev dividesT (d n : myN) : Type := Σ k : myN, (d * k) ≡ n

-- Every element of `dividesT d n` gives a proof of `divides d n` of chapter7.lean.
def divides_of_dividesT {d n : myN} (p : dividesT d n) : divides d n :=
  Nonempty.intro p

-- n ∣ n
def dividesT_refl (n : myN) : dividesT n n := ⟨_1, mulN_one_right n⟩

-- n ∣ 0
def dividesT_zero (n : myN) : dividesT n myN.zero := ⟨myN.zero, MyEq.refl _⟩

-- 1 ∣ n
def one_dividesT (n : myN) : dividesT _1 n := ⟨n, mulN_one_left n⟩

-- 0 ∣ n  →  n = 0
def eq_zero_of_zero_dividesT (n : myN) : dividesT myN.zero n → (n ≡ myN.zero)
  | ⟨k, p⟩ => (myEq_symm p) • (mulN_zero_left k)

-- a ∣ b and b ∣ c  →  a ∣ c
def dividesT_trans {a b c : myN} : dividesT a b → dividesT b c → dividesT a c
  | ⟨k, p⟩, ⟨l, q⟩ =>
      ⟨k * l, (myEq_symm (mulN_assoc a k l)) • ((ap (fun x => x * l) _ _ p) • q)⟩

-- a ∣ a · b
def dividesT_mul_right_self (a b : myN) : dividesT a (a * b) := ⟨b, MyEq.refl _⟩

-- b ∣ a · b
def dividesT_mul_left_self (a b : myN) : dividesT b (a * b) := ⟨a, mulN_comm b a⟩

-- d ∣ a  →  d ∣ a · b
def dividesT_mul_right {d a : myN} (b : myN) : dividesT d a → dividesT d (a * b)
  | ⟨k, p⟩ => ⟨k * b, (myEq_symm (mulN_assoc d k b)) • (ap (fun x => x * b) _ _ p)⟩

-- Proposition 7.1.5: if d divides two of the numbers a, b, a + b, then it divides
-- the third one.

-- d ∣ a and d ∣ b  →  d ∣ a + b
def dividesT_add {d a b : myN} : dividesT d a → dividesT d b → dividesT d (a + b)
  | ⟨k, p⟩, ⟨l, q⟩ => ⟨k + l, (mulN_distrib_left d k l) • (ap2 (fun (x y : myN) => x + y) p q)⟩

-- d ∣ a and d ∣ a + b  →  d ∣ b
def dividesT_add_cancel_left {d a b : myN} : dividesT d a → dividesT d (a + b) → dividesT d b
  | ⟨k, p⟩, ⟨l, q⟩ => ⟨dist l k, (mulN_dist d l k) • ((ap2 dist q p) • dist_add_self a b)⟩

-- d ∣ b and d ∣ a + b  →  d ∣ a
def dividesT_add_cancel_right {d a b : myN} (p : dividesT d b) (q : dividesT d (a + b)) :
    dividesT d a :=
  dividesT_add_cancel_left p (transport (fun x => dividesT d x) (addN_comm a b) q)

-- If d ∣ n and n ≠ 0, then d ≤ n.
def leqN_of_dividesT (d n : myN) (h : myNegType (n ≡ myN.zero)) : dividesT d n → leqN d n
  | ⟨myN.zero, p⟩ => Empty.elim (h (myEq_symm p))
  | ⟨myN.succ k, p⟩ => transport (fun x => leqN d x) p (leqN_mul_succ_right d k)

-- d ∣ 1  →  d = 1
def eq_one_of_dividesT_one : (d : myN) → dividesT d _1 → (d ≡ _1)
  | myN.zero, p => Empty.elim (succN_neq_zero _ (eq_zero_of_zero_dividesT _1 p))
  | myN.succ myN.zero, _ => MyEq.refl _
  | myN.succ (myN.succ _), p => Empty.elim (leqN_of_dividesT _ _1 (succN_neq_zero _) p)

-- Exercise 7.2: divisibility is antisymmetric.
def dividesT_antisymm : (m n : myN) → dividesT m n → dividesT n m → (m ≡ n)
  | myN.zero, n, p, _ => myEq_symm (eq_zero_of_zero_dividesT n p)
  | myN.succ _, myN.zero, _, q => eq_zero_of_zero_dividesT _ q
  | myN.succ m, myN.succ n, p, q =>
      leqN_antisymm _ _ (leqN_of_dividesT _ _ (succN_neq_zero n) p)
                        (leqN_of_dividesT _ _ (succN_neq_zero m) q)


/- ###################################################################### -/
/-  The factorial function (defined in chapter3_naturals_with_zero.lean)   -/
/- ###################################################################### -/

def factorial_neq_zero : (n : myN) → myNegType (factorial n ≡ myN.zero)
  | myN.zero => succN_neq_zero _
  | myN.succ n => fun p => factorial_neq_zero n (proj2 (addN_eq_zero _ _ p))

-- Exercise 7.3: if 0 < k ≤ n, then k ∣ n!
def dividesT_factorial : (n k : myN) → myNegType (k ≡ myN.zero) → leqN k n →
    dividesT k (factorial n)
  | myN.zero, k, hk, p => Empty.elim (hk (leqN_zero k p))
  | myN.succ n, k, hk, p =>
      match leqN_succ_cases k n p with
      | Sum.inl q => dividesT_mul_right (myN.succ n) (dividesT_factorial n k hk q)
      | Sum.inr q =>
          transport (fun x => dividesT x (factorial (myN.succ n))) (myEq_symm q)
            (dividesT_mul_left_self (factorial n) (myN.succ n))

-- n ≤ n!
def leqN_factorial : (n : myN) → leqN n (factorial n)
  | myN.zero => ()
  | myN.succ n =>
      leqN_of_dividesT _ _ (factorial_neq_zero _)
        (dividesT_factorial (myN.succ n) (myN.succ n) (succN_neq_zero n) (leqN_refl _))


/- ###################################################################### -/
/-  Euclidean division (Exercise 7.9)                                      -/
/- ###################################################################### -/

-- For d ≠ 0 and every n there are q and r < d with n = d · q + r.
def euclidean_division (d : myN) (hd : myNegType (d ≡ myN.zero)) :
    (n : myN) → Σ q : myN, Σ r : myN, myProd (ltN r d) (n ≡ ((d * q) + r))
  | myN.zero =>
      ⟨myN.zero, myN.zero, myProd.mk (zero_ltN_of_neq_zero d hd) (MyEq.refl _)⟩
  | myN.succ n =>
      match euclidean_division d hd n with
      | ⟨q, r, myProd.mk hr e⟩ =>
          match ltN_succ_cases r d hr with
          | Sum.inl h => ⟨q, myN.succ r, myProd.mk h (ap myN.succ _ _ e)⟩
          | Sum.inr h =>
              ⟨myN.succ q, myN.zero,
                myProd.mk (zero_ltN_of_neq_zero d hd)
                  ((ap myN.succ _ _ e) • (ap (fun x => (d * q) + x) _ _ h))⟩


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
