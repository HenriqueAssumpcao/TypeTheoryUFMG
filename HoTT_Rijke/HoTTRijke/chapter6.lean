-- This file contains implementation for universes and
-- natural/integer arithmetc for zero-based naturals using observational
-- equality.

import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5_props_naturals_with_zero

open chapter5_myeq
open chapter3_booleans
open chapter4_coproducts
open chapter4_booleans
open chapter3_naturals_with_zero
open props_naturals_with_zero

namespace chapter6_Universes

-- Observational Equality

def E0 (n : myN) : Type :=   -- (0 = n)
  match n with
  | myN.zero => Unit
  | myN.succ _ => Empty

def ES (n : myN) (X : myN → Type) (m : myN) : Type :=    -- (S(n) = m)
  match n, m with
  | _, myN.zero => Empty
  | _, myN.succ m' => X m'

def Eq_N (n m : myN): Type :=
  match n with
  | myN.zero => E0 m
  | myN.succ n' => ES n' (Eq_N n') m

-- Alternative definition of Eq_N using pattern matching on both arguments
/-
def Eq_N (m n : myN) : Type :=
  match m, n with
  | myN.zero, myN.zero => Unit
  | myN.zero, myN.succ _ => Empty
  | myN.succ _, myN.zero => Empty
  | myN.succ m, myN.succ n => Eq m n
-/


-- Lemma 6.3.2
-- Eq_N is reflexive

def refl_Eq_N (n : myN) : Eq_N n n :=
  match n with
  | myN.zero => ()
  | myN.succ n' => refl_Eq_N n'


-- Proposition 6.3.3
-- Eq_N is equivalent to MyEq

def Equality_Equiv (m n : myN) (p : m ≡ n) : Eq_N m n :=
  let P := fun x : myN => fun _ : m ≡ x => Eq_N m x
  ind_eq P (refl_Eq_N m) n p                              -- Using induction principle

def Equality_Equiv_conv (p : Eq_N m n) : m ≡ n :=
  match m, n with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ _ => Empty.elim p
  | myN.succ _, myN.zero => Empty.elim p
  | myN.succ _, myN.succ _ => ap myN.succ _ _ (Equality_Equiv_conv p)   -- (Eq_N m n) = (Eq_N m.succ n.succ)



-- Theorem 6.4.1
-- Peano's seventh axiom (m ≡ n  ↔  m+1 ≡ n+1)

def P7 (m n : myN) (p : m ≡ n) : m.succ ≡ n.succ :=
  Equality_Equiv_conv (Equality_Equiv m n p)    -- (m ≡ n) → (Eq_N m n) = (Eq_N m+1 n+1) → m+1 ≡ n+1

def P7_conv (m n : myN) (p : m.succ ≡ n.succ) : m ≡ n :=
  Equality_Equiv_conv (Equality_Equiv m.succ n.succ p)


-- Theorem 6.4.2
-- Peano's eight axiom (0 ≠ n+1)

def P8 (n : myN) (p : myN.zero ≡ n.succ) : Empty :=
  Equality_Equiv myN.zero n.succ p





-- ######################## Exercises ############################ --


-- 6.1
-- a)

-- (𝑚 = 𝑛) ↔ (𝑚 + 𝑘 = 𝑛 + 𝑘)
def add_natural_to_equals (k : myN) (p : m ≡ n) : (myAdd m k) ≡ (myAdd n k) :=
  match k with
  | myN.zero => p
  | myN.succ k => ap myN.succ _ _ (add_natural_to_equals k p)

def add_nat_injective (p : (myAdd m k) ≡ (myAdd n k)) : m ≡ n :=
  match k with
  | myN.zero => p
  | myN.succ _ => add_nat_injective (P7_conv _ _ p)

-- (𝑚 = 𝑛) ↔ (𝑚 · (𝑘 + 1) = 𝑛 · (𝑘 + 1))
example (k : myN) (p : m ≡ n) :  (myMult m (myN.succ k)) ≡ (myMult n (myN.succ k)) :=
  ap (fun x : myN => myMult x (myN.succ k)) _ _ p

def mult_succ_injective (p : (myMult m (myN.succ k)) ≡ (myMult n (myN.succ k))) : m ≡ n :=
  match m, n with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ n =>
    have p' : myN.zero ≡ myN.succ (myAdd (myMult n k.succ) k) :=
      (myEq_symm (myMult_zero_left k.succ)) • p • (myMult_succ_left n k.succ)     -- 0 = 0·(k+1) = (n+1)(k+1) = n(k+1)+(k+1) = (n(k+1)+k)+1

    Empty.elim (Equality_Equiv _ _ p')                                            -- (0 = x+1) ≡ ∅

  | myN.succ m, myN.zero =>
    have p' : myN.zero ≡ myN.succ (myAdd (myMult m k.succ) k) :=
      (myEq_symm (myMult_zero_left k.succ)) • (myEq_symm p) • (myMult_succ_left m k.succ)

    Empty.elim (Equality_Equiv _ _ p')

  | myN.succ m, myN.succ n =>
    have h : (myMult k.succ m.succ) ≡ (myMult k.succ n.succ) :=
      (myMult_comm k.succ m.succ) • p • (myMult_comm n.succ k.succ)               -- (k+1)(m+1) = (m+1)(k+1) = (n+1)(k+1) = (k+1)(n+1)
    have p' : myAdd (myMult k.succ m) k.succ ≡ myAdd (myMult k.succ n) k.succ :=
      (myAdd_commutative _ _) • h • (myAdd_commutative _ _)
    have h' : (myMult m k.succ) ≡ (myMult n k.succ) :=
      (myMult_comm m k.succ) • (add_nat_injective p') • (myMult_comm k.succ n)    -- m(k+1) = (k+1)m = (k+1)n = n(k+1)

    Equality_Equiv_conv (Equality_Equiv m n (mult_succ_injective h'))             -- (m = n) → (m+1 = n+1)


-- b)

-- 𝑚 + 𝑛 = 0 ↔ (𝑚 = 0) e (𝑛 = 0)
example (p : m ≡ myN.zero) (q : n ≡ myN.zero) : (myAdd m n) ≡ myN.zero := (ap (myAdd m) _ _ q) • p

def sum_equals_zero (p : (myAdd m n) ≡ myN.zero) : myProd (m ≡ myN.zero) (n ≡ myN.zero) :=
  match n with
  | myN.zero => myProd.mk p (MyEq.refl _)
  | myN.succ _ => Empty.elim (Equality_Equiv _ _ p)

-- 𝑚 · 𝑛 = 0  <=> (𝑚 = 0) ou (𝑛 = 0)
def mult_equals_zero (p : (m × n) ≡ myN.zero) : mySum (m ≡ myN.zero) (n ≡ myN.zero) :=
  match n with
  | myN.zero => mySum.inr (MyEq.refl _)
  | myN.succ n =>
    have h : myAdd (m × n) m ≡ myN.zero := (myAdd_commutative _ _) • p    -- (m·n)+m = m+(m·n) =  m(n+1) = 0
    mySum.inl (proj2 (sum_equals_zero h))

def mult_by_zero (x : mySum (m ≡ myN.zero) (n ≡ myN.zero)) : (m × n) ≡ myN.zero :=
  match x with
  | mySum.inl x => (ap (fun y : myN => myMult y n) _ _ x) • (myMult_zero_left n)    -- (m = 0) => (m·n = 0·n = 0)
  | mySum.inr x => ap (myMult m) _ _ x

-- 𝑚·𝑛 = 1 <=> (𝑚 = 1) e (𝑛 = 1)
def mult_one_by_one (p : myProd (m ≡ myN.zero.succ) (n ≡ myN.zero.succ)) : (m × n) ≡ myN.zero.succ :=
  calc
    -- m·n = m(0+1) = m + m·0 = m + 0 = m = 0 + 1 = 1
    (m × n) ≡ m := ap (myMult m) _ _ (proj2 p)
    _ ≡ myN.zero.succ := proj1 p

def mult_equals_one (p : (m × n) ≡ myN.zero.succ) : myProd (m ≡ myN.zero.succ) (n ≡ myN.zero.succ) :=
  match m, n with
  | _, myN.zero => Empty.elim (Equality_Equiv _ _ p)
  | myN.zero, _ => Empty.elim (Equality_Equiv _ _ ((myMult_comm _ _) • p))

  | myN.succ m, myN.succ n =>
    have h : (myAdd m (m.succ × n)).succ ≡  myN.zero.succ := (myEq_symm (left_successor_law_add _ _)) • p
    have h1: myAdd m (m.succ × n) ≡ myN.zero :=
      Equality_Equiv_conv (Equality_Equiv (myAdd m (m.succ × n)).succ myN.zero.succ h)

    have h2 : mySum (m.succ ≡ myN.zero) (n ≡ myN.zero) := mult_equals_zero (proj2 (sum_equals_zero h1))

    have m0 : m ≡ myN.zero := proj1 (sum_equals_zero h1)
    match h2 with
    | mySum.inr n0 =>
      myProd.mk (Equality_Equiv_conv (Equality_Equiv m myN.zero m0))
      (Equality_Equiv_conv (Equality_Equiv n myN.zero n0))

    | mySum.inl m1 => Empty.elim (Equality_Equiv _ _ m1)


-- c)

-- 𝑚 ≠ 𝑚 + (𝑛 + 1)
def add_dont_fix (p : m ≡ myAdd m (myN.succ n)) : Empty :=
  match m with
  | myN.zero => Empty.elim (P8 _ (p • (myAdd_zero_left n.succ))) -- 0 = 0 + (n+1) = n+1
  | myN.succ m =>
    -- m+1 = (m+1) + (n+1) = (n+1) + (m+1) = ((n+1) + m) + 1 → m = (n+1) + m = m + (n+1) → ∅
    have h : m.succ ≡ (myAdd (n.succ) m).succ := p • (myAdd_commutative _ _)
    have h1 : m ≡ myAdd m n.succ :=
      (Equality_Equiv_conv (Equality_Equiv m.succ ((myAdd (n.succ) m).succ) h)) • (myAdd_commutative _ _)

    Empty.elim (add_dont_fix h1)

-- 𝑚 + 1 ≠ (𝑚 + 1)(𝑛 + 2)
def mult_dont_fix (p : (myN.succ m) ≡ (myN.succ m) × (myN.succ (myN.succ n))) : Empty :=
  match m  with
  | myN.zero =>
    -- 0+1 = (0+1)·((n+1)+1) = (0+1) + (0+1)(n+1) = (0+1)(n+1) + (0+1) = (0+1)(n+1) + 1 → 0 = (0+1)(n+1) → (0+1) = 0 ou (n+1) = 0
    have h : myN.zero.succ ≡ (myN.zero.succ × n.succ).succ := p • (myAdd_commutative _ _)
    have h1 : myN.zero ≡ myN.zero.succ × n.succ := Equality_Equiv_conv (Equality_Equiv myN.zero.succ _ h)
    have h2 := mult_equals_zero (myEq_symm h1)
    match h2 with
    | mySum.inl k => Empty.elim (Equality_Equiv _ _ k)
    | mySum.inr k => Empty.elim (Equality_Equiv _ _ k)

  | myN.succ m =>
    -- (m+1)+1 = ((m+1)+1)((n+1)+1) = ((m+1)+1) + ((m+1)+1)(n+1) = ((m+1) + ((m+1)+1)(n+1)) + 1 → m+1 = (m+1) + (m+1)+1)(n+1)
    have h : m.succ ≡ (myAdd m.succ (m.succ.succ × n.succ)) :=
      Equality_Equiv_conv (Equality_Equiv m.succ.succ _ (p • (left_successor_law_add _ _)))

    -- (m+1) + ((m+1)+1)(n+1) = (m+1) + ((m+1)+1) + ((m+1)+1)n = (m+1) + (((m+1) + ((m+1)+1)n) + 1)
    have h1 : (myAdd m.succ (m.succ.succ × n.succ)) ≡ myAdd m.succ (myAdd m.succ (m.succ.succ × n)).succ :=
      ap (myAdd m.succ) _ _ (left_successor_law_add _ _)

    add_dont_fix (h • h1)


-- 6.2
-- a)

def Eq_bool (b1 b2 : myBool) : Type :=
  match b1, b2 with
  | myBool.myTrue, myBool.myTrue => Unit
  | myBool.myFalse, myBool.myFalse => Unit
  | _, _ => Empty

def Eq_bool_refl (b : myBool) : Eq_bool b b :=
  match b with
  | myBool.myTrue => ()
  | myBool.myFalse => ()


-- b)

def Eq_bool_equiv (b1 b2 : myBool) (p : Eq_bool b1 b2) : (b1 ≡ b2) :=
  match b1, b2 with
  | myBool.myTrue, myBool.myTrue => MyEq.refl _
  | myBool.myFalse, myBool.myFalse => MyEq.refl _
  | myBool.myFalse, myBool.myTrue => Empty.elim p
  | myBool.myTrue, myBool.myFalse => Empty.elim p

def Eq_bool_equiv_conv (b1 b2 : myBool) (p : b1 ≡ b2) : Eq_bool b1 b2 :=
  let P := fun x : myBool => fun _ : b1 ≡ x => Eq_bool b1 x
  ind_eq P (Eq_bool_refl b1) b2 p


-- c)

def neg_injective (b : myBool) (p : Eq_bool b (myNeg b)) : Empty :=
  match b with
  | myBool.myTrue => Empty.elim p
  | myBool.myFalse => Empty.elim p


-- 6.3

def leq (m n : myN) : Type :=
  match m, n with
  | myN.zero, _ => Unit
  | myN.succ _, myN.zero => Empty
  | myN.succ m, myN.succ n => leq m n

-- a)

def leq_refl (n : myN) : leq n n :=
  match n with
  | myN.zero => ()
  | myN.succ n => leq_refl n

def leq_antisymm (m n : myN) (p : leq m n) (q : leq n m) : m ≡ n :=
  match m, n with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ _ => Empty.elim q
  | myN.succ _, myN.zero => Empty.elim p
  | myN.succ m, myN.succ n => ap myN.succ _ _ (leq_antisymm m n p q)

def leq_trans (m n k : myN) (p : leq m n) (q : leq n k) : leq m k :=
  match m, n, k with
  | myN.zero, _, _ => ()
  | myN.succ _, myN.zero, _ => Empty.elim p
  | myN.succ _, myN.succ _, myN.zero => Empty.elim q
  | myN.succ m, myN.succ n, myN.succ k => leq_trans m n k p q


--b)

def leq_total (m n : myN) : mySum (leq m n) (leq n m) :=
  match m, n with
  | myN.zero, _ => mySum.inl ()
  | myN.succ _, myN.zero => mySum.inr ()
  | myN.succ m, myN.succ n =>
    match leq_total m n with
    | mySum.inl p => mySum.inl p
    | mySum.inr q => mySum.inr q


-- c)

def add_leq (m n k : myN) (p : leq m n) : leq (myAdd m k) (myAdd n k) :=
  match k with
  | myN.zero => p
  | myN.succ k => add_leq m n k p

def add_leq_conv (m n k : myN) (p : leq (myAdd m k) (myAdd n k)) : leq m n :=
  match k with
  | myN.zero => p
  | myN.succ k => add_leq_conv m n k p


-- d)

def leq_equals (m n : myN) (p : m ≡ n) : leq m n :=
  match m, n with
  | myN.zero, myN.zero => ()
  | myN.zero, myN.succ _ => Empty.elim (Equality_Equiv _ _ p)
  | myN.succ _, myN.zero => Empty.elim (Equality_Equiv _ _ (myEq_symm p))
  | myN.succ m, myN.succ n => leq_equals m n (Equality_Equiv_conv (Equality_Equiv m.succ n.succ p))

def mult_succ_leq (m n k : myN) (p : leq m n) : leq (m × k) (n × k) :=
  match k with
  | myN.zero => ()
  | myN.succ k =>
    -- m ≤ n => mk ≤ nk => mk + m ≤ nk + m => m + mk ≤ nk + m => m + mk ≤ m + nk => m + mk ≤ n + nk
    have h_comm_left : leq (myAdd m (m × k)) (myAdd (m × k) m) :=
      leq_equals _ _ (myAdd_commutative _ _)

    have h_add_leq : leq (myAdd (m × k) m) (myAdd (n × k) m) :=
      add_leq _ _ m (mult_succ_leq m n k p)

    have h_left : leq (myAdd m (m × k)) (myAdd (n × k) m) :=      -- (m + mk ≤ mk + m) and (mk + m ≤ nk + m) => (m + mk ≤ nk + m)
      leq_trans _ _ _ h_comm_left h_add_leq

    have h_comm_right : leq (myAdd (n × k) m) (myAdd m (n × k)) :=
      leq_equals _ _ (myAdd_commutative _ _)

    have h_middle : leq (myAdd m (m × k)) (myAdd m (n × k)) :=    -- (nk + m ≤ m + nk) and (m + mk ≤ nk + m) => (m + mk ≤ m + nk)
      leq_trans _ _ _ h_left h_comm_right

    have h_final : leq (myAdd m (n × k)) (myAdd n (n × k)) :=     -- (m < n) and (m + mk ≤ m + nk) => (m + mk ≤ n + nk)
      add_leq m n (n × k) p

    leq_trans _ _ _ h_middle h_final

def mult_succ_leq_conv (m n k : myN) (p : leq (m × k.succ) (n × k.succ)) : leq m n :=
  let h := leq_total m n
  match h with
  | mySum.inl p => p
  | mySum.inr q =>
    have h1 : leq (n × k.succ) (m × k.succ) := mult_succ_leq n m k.succ q
    have h2 : (m × k.succ) ≡ (n × k.succ) := leq_antisymm _ _ p h1
    have h3 : m ≡ n := mult_succ_injective h2
    have h4 : leq m n := leq_equals _ _ h3
    h4


-- e)

-- 𝑘 ≤ min(𝑚, 𝑛) ↔ (𝑘 ≤ 𝑚) e (𝑘 ≤ 𝑛)
def leq_min (k m n : myN) (p : leq k (N_min m n)) : myProd (leq k m) (leq k n) :=
  match k with
  | myN.zero => myProd.mk () ()
  | myN.succ k =>
    match m, n with
    | myN.zero, n =>
    have h : (N_min myN.zero n) ≡ myN.zero :=
      match n with
      | myN.zero => MyEq.refl _
      | myN.succ _ => MyEq.refl _

    have h1 : leq k.succ myN.zero := leq_trans k.succ (N_min myN.zero n) myN.zero p (leq_equals (N_min myN.zero n) myN.zero h)
    myProd.mk (leq_trans _ _ _ h1 ()) (leq_trans _ _ _ h1 ())

    | m, myN.zero =>
    have h : (N_min m myN.zero) ≡ myN.zero :=
      match m with
      | myN.zero => MyEq.refl _
      | myN.succ _ => MyEq.refl _

    have h1 : leq k.succ myN.zero := leq_trans k.succ (N_min m myN.zero) myN.zero p (leq_equals (N_min m myN.zero) myN.zero h)
    myProd.mk (leq_trans _ _ _ h1 ()) (leq_trans _ _ _ h1 ())

    | myN.succ m, myN.succ n =>
      let h := leq_min k m n p
      myProd.mk (proj1 h) (proj2 h)

def leq_min_conv (k m n : myN) (p : myProd (leq k m) (leq k n)) : leq k (N_min m n) :=
  match k with
  | myN.zero => ()
  | myN.succ k =>
    match m, n with
    | myN.zero, _ => Empty.elim (proj1 p)
    | _, myN.zero => Empty.elim (proj2 p)
    | myN.succ m, myN.succ n => leq_min_conv k m n (myProd.mk (proj1 p) (proj2 p))

-- Lemmas
def leq_zero (n : myN) (p : leq n myN.zero): n ≡ myN.zero :=
  match n with
  | myN.zero => MyEq.refl _
  | myN.succ _ => Empty.elim p

def max_equals_zero (m n : myN) (p : (N_max m n) ≡ myN.zero) : myProd (m ≡ myN.zero) (n ≡ myN.zero) :=
  match m, n with
  | myN.zero, myN.zero => myProd.mk (MyEq.refl _) (MyEq.refl _)
  | myN.zero, myN.succ _ => Empty.elim (Equality_Equiv _ _ p)
  | myN.succ _, myN.zero => Empty.elim (Equality_Equiv _ _ p)
  | myN.succ _, myN.succ _ => Empty.elim (Equality_Equiv _ _ p)

-- 𝑘 ≥ max(𝑚, 𝑛) ↔ (𝑘 ≥ 𝑚) e (𝑘 ≥ 𝑛)
def leq_max (k m n : myN) (p : leq (N_max m n) k) : myProd (leq m k) (leq n k) :=
  match k with
  | myN.zero =>
    have h1 : myProd (m ≡ myN.zero) (n ≡ myN.zero) := max_equals_zero m n (leq_zero (N_max m n) p)
    myProd.mk (leq_equals _ _ (proj1 h1)) (leq_equals _ _ (proj2 h1))

  | myN.succ k =>
    match m, n with
    | myN.zero, n =>
    have h1 : n ≡ N_max myN.zero n :=
      match n with
      | myN.zero => MyEq.refl _
      | myN.succ _ => MyEq.refl _
    have h2 : leq n k.succ := leq_trans _ _ _ (leq_equals n (N_max myN.zero n) h1) p
    myProd.mk () h2

    | m, myN.zero =>
    have h1 : m ≡ N_max m myN.zero :=
      match m with
      | myN.zero => MyEq.refl _
      | myN.succ _ => MyEq.refl _
    have h2 : leq m k.succ := leq_trans _ _ _ (leq_equals m (N_max m myN.zero) h1) p
    myProd.mk h2 ()

    | myN.succ m, myN.succ n =>
      let h := leq_max k m n p
      myProd.mk (proj1 h) (proj2 h)

def leq_max_conv (k m n : myN) (p : myProd (leq m k) (leq n k)) : leq (N_max m n) k :=
  match m, n with
  | myN.zero, n =>
  have h1 : N_max myN.zero n ≡ n :=
    match n with
      | myN.zero => MyEq.refl _
      | myN.succ _ => MyEq.refl _

  leq_trans _ _ _ (leq_equals (N_max myN.zero n) n h1) (proj2 p)

  | m, myN.zero =>
  have h1 : N_max m myN.zero ≡ m :=
    match m with
      | myN.zero => MyEq.refl _
      | myN.succ _ => MyEq.refl _

  leq_trans _ _ _ (leq_equals (N_max m myN.zero) m h1) (proj1 p)

  | myN.succ m, myN.succ n =>
    match k with
    | myN.zero => Empty.elim (proj1 p)
    | myN.succ k => leq_max_conv k m n (myProd.mk (proj1 p) (proj2 p))


-- 6.4

def less_than (m n : myN) : Type :=
  match m, n with
  | _, myN.zero => Empty
  | myN.zero, myN.succ _ => Unit
  | myN.succ m, myN.succ n => less_than m n


-- a)

def less_than_antiref (n : myN) (p : less_than n n): Empty :=
  match n with
  | myN.zero => Empty.elim p
  | myN.succ n => less_than_antiref n p

def less_than_nonsymm (m n : myN) (p : less_than m n) (q : less_than n m) : Empty :=
  match m, n with
  | myN.zero, myN.zero => Empty.elim p
  | myN.zero, myN.succ _ => Empty.elim q
  | myN.succ _, myN.zero => Empty.elim p
  | myN.succ m, myN.succ n => less_than_nonsymm m n p q

def less_than_trans (m n k : myN) (p : less_than m n) (q : less_than n k) : less_than m k :=
  match m, n, k with
  | myN.zero, _, myN.succ _ => ()
  | myN.zero , myN.zero, myN.zero => Empty.elim q
  | myN.succ _, myN.zero, _ => Empty.elim p
  | myN.succ _, myN.succ _, myN.zero => Empty.elim q
  | myN.succ m, myN.succ n, myN.succ k => less_than_trans m n k p q


-- b)

def less_than_succ (n : myN) : less_than n n.succ :=
  match n with
  | myN.zero => ()
  | myN.succ n => less_than_succ n

def less_than_sum_succ (m n : myN) (p : less_than m n) : less_than m n.succ := less_than_trans _ _ _ p (less_than_succ n)


-- c)

-- 𝑚 < 𝑛 ↔ (𝑚 + 1 ≤ 𝑛)
def less_than_leq (m n : myN) (p : less_than m n) : leq m n :=
  match m, n with
  | myN.zero, _ => ()
  | myN.succ _, myN.zero => Empty.elim p
  | myN.succ m, myN.succ n => less_than_leq m n p

def less_than_leq_conv (m n : myN) (p : leq m.succ n) : less_than m n :=
  match m, n with
  | _, myN.zero => Empty.elim p
  | myN.zero, myN.succ _ => ()
  | myN.succ m, myN.succ n => less_than_leq_conv m n p

-- 𝑚 < 𝑛 ↔ (𝑚 ≤ 𝑛) e (𝑚 ≠ 𝑛)
def less_than_leq_law (m n : myN) (p : less_than m n) : myProd (leq m n) ((m ≡ n) → Empty) :=
  match m, n with
  | myN.zero, myN.zero => Empty.elim p
  | myN.zero, myN.succ _ => myProd.mk () (fun x => Empty.elim (Equality_Equiv _ _ x))
  | myN.succ m, myN.succ n =>
    let h := less_than_leq_law m n p
    myProd.mk (proj1 h) (fun x => proj2 h (Equality_Equiv_conv (Equality_Equiv m.succ n.succ x)))

def less_than_leq_law_conv (m n : myN) (p : myProd (leq m n) ((m ≡ n) → Empty)) : less_than m n :=
  match m, n with
  | myN.zero, myN.zero => Empty.elim (proj2 p (MyEq.refl _))
  | myN.zero, myN.succ _ => ()
  | myN.succ m, myN.succ n =>
    less_than_leq_law_conv m n (myProd.mk (proj1 p) (fun x => proj2 p (Equality_Equiv_conv (Equality_Equiv m n x))))


-- 6.5

def dist (m n : myN) : myN :=
  match m, n with
  | myN.zero, n => n
  | m, myN.zero => m
  | myN.succ m, myN.succ n => dist m n

-- a)

-- (i)  m ≡ n ↔ dist(m, n) ≡ 0
def dist_equals (m n : myN) (p : m ≡ n) : (dist m n) ≡ myN.zero :=
  match m, n with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ _ => Empty.elim (Equality_Equiv _ _ p)
  | myN.succ _, myN.zero => Empty.elim (Equality_Equiv _ _ (myEq_symm p))
  | myN.succ m, myN.succ n => dist_equals m n (Equality_Equiv_conv (Equality_Equiv m.succ n.succ p))

def dist_equals_conv (m n : myN) (p : (dist m n) ≡ myN.zero) : m ≡ n :=
  match m, n with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ _ => Empty.elim (Equality_Equiv _ _ p)
  | myN.succ _, myN.zero => Empty.elim (Equality_Equiv _ _ (myEq_symm p))
  | myN.succ m, myN.succ n =>
    Equality_Equiv_conv (Equality_Equiv m n (dist_equals_conv m n (Equality_Equiv_conv (Equality_Equiv (dist m n) myN.zero p))))

-- (ii)  dist(m, n) ≡ dist(n, m)
def dist_commutative (m n : myN) : (dist m n) ≡ (dist n m) :=
  match m, n with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ _ => MyEq.refl _
  | myN.succ _, myN.zero => MyEq.refl _
  | myN.succ m, myN.succ n => dist_commutative m n

def dist_triangle_inequality (m n k : myN): leq (dist m n) (myAdd (dist m k) (dist k n)) := sorry




-- Aditional propositions about dist

def dist_from_zero (n : myN) : dist n _0 ≡ n :=
  match n with
  | myN.zero => MyEq.refl _
  | myN.succ _ => MyEq.refl _

def dist_equals_0 (n : myN) : dist n n ≡ _0 :=
  match n with
  | myN.zero => MyEq.refl _
  | myN.succ n' =>dist_equals_0 n'

def dist_of_equals (m n : myN) (p : m ≡ n) : (dist m n) ≡ myN.zero := by
  have h : (dist m n) ≡ (dist m m) := ap (fun x => dist m x) _ _ (myEq_symm p)
  exact h • dist_equals_0 m

def dist_symm (n1 n2 : myN) : dist n1 n2 ≡ dist n2 n1 :=
  match n1, n2 with
  | myN.zero, myN.zero => MyEq.refl _
  | myN.zero, myN.succ _ => MyEq.refl _
  | myN.succ _, myN.zero => MyEq.refl _
  | myN.succ n1', myN.succ n2' =>
      calc
        dist (myN.succ n1') (myN.succ n2') ≡ dist n1' n2' := MyEq.refl _
        _ ≡ dist n2' n1' := dist_symm n1' n2'
        _ ≡ dist (myN.succ n2') (myN.succ n1') := MyEq.refl _


def add_dist_of_leq (m n : myN) (p : leq m n) :
    myAdd m (dist m n) ≡ n :=
  match m, n with
  | myN.zero, n =>
    calc
      myAdd myN.zero (dist myN.zero n) ≡ dist myN.zero n := myAdd_zero_left _
      _ ≡ n := dist_commutative _ _ • (dist_from_zero n)

  | myN.succ _, myN.zero =>
      Empty.elim p

  | myN.succ m, myN.succ n =>
      calc
        myAdd m.succ (dist m.succ n.succ)
            ≡ myAdd (dist m n) m.succ :=
              myAdd_commutative _ _
        _ ≡ (myAdd (dist m n) m).succ :=
              MyEq.refl _
        _ ≡ n.succ :=
              ap myN.succ _ _
                ((myEq_symm (myAdd_commutative m (dist m n))) •
                  add_dist_of_leq m n p)


def dist_transitivity (x y z : myN) :
    mySum
      (myAdd (dist x y) (dist y z) ≡ dist x z)
      (mySum
        (myAdd (dist y z) (dist x z) ≡ dist x y)
        (myAdd (dist x z) (dist x y) ≡ dist y z)) :=
  match x, y, z with

  | myN.zero, y, z =>
      match leq_total y z with

      | mySum.inl hyz =>
        have h :=
          calc
            myAdd (dist myN.zero y) (dist y z) ≡ myAdd y (dist y z) := ap (fun t => myAdd t (dist y z)) _ _ (dist_commutative _ _ • (dist_from_zero y))
            _ ≡ z := (add_dist_of_leq y z hyz)
            _ ≡ dist myN.zero z := myEq_symm (dist_commutative _ _ • (dist_from_zero z))

        mySum.inl h

      | mySum.inr hzy =>
          mySum.inr (
            mySum.inl (
              calc
                myAdd (dist y z) (dist myN.zero z) ≡ myAdd (dist z y) (dist myN.zero z) := ap (fun t => myAdd t (dist myN.zero z)) _ _ (dist_symm y z)
                _ ≡ myAdd (dist myN.zero z) (dist z y) := myAdd_commutative _ _
                _ ≡ myAdd z (dist z y) := ap (fun t => myAdd t (dist z y)) _ _ (dist_commutative _ _ • (dist_from_zero z))
                _ ≡ y := add_dist_of_leq z y hzy
                _ ≡ dist myN.zero y := myEq_symm (dist_commutative _ _ • (dist_from_zero y))
            )
          )



  | x, myN.zero, z =>
      match leq_total x z with

      | mySum.inl hxz =>
          mySum.inr (
            mySum.inr (
              calc
                myAdd (dist x z) (dist x myN.zero) ≡ myAdd (dist x myN.zero) (dist x z) := myAdd_commutative _ _
                _ ≡ myAdd x (dist x z) := ap (fun t => myAdd t (dist x z)) _ _ (dist_from_zero x)
                _ ≡ z := add_dist_of_leq x z hxz
                _ ≡ dist myN.zero z := myEq_symm (dist_commutative _ _ • (dist_from_zero z))
            )
          )

      | mySum.inr hzx =>
          mySum.inr (
            mySum.inl (
              -- myAdd (dist myN.zero z) (dist x z) ≡ dist x myN.zero
              calc
                myAdd (dist myN.zero z) (dist x z) ≡ myAdd z (dist x z) := ap (fun t => myAdd t (dist x z)) _ _ (dist_commutative _ _ • (dist_from_zero z))
                _ ≡ myAdd (dist x z) z := myAdd_commutative _ _
                _ ≡ myAdd (dist z x) z := ap (fun t => myAdd t z) _ _ (dist_symm x z)
                _ ≡ x := (myAdd_commutative _ _) • add_dist_of_leq z x hzx
                _ ≡ dist x myN.zero := myEq_symm (dist_commutative _ _ • (dist_commutative _ _ • dist_from_zero x))
            )
          )

  | x, y, myN.zero =>
      match leq_total x y with

      | mySum.inl hxy =>
          mySum.inr (
            mySum.inr (
              calc
                 myAdd (dist x myN.zero) (dist x y) ≡ myAdd x (dist x y) := ap (fun t => myAdd t (dist x y)) _ _ (dist_from_zero x)
                 _ ≡ y := add_dist_of_leq x y hxy
                 _ ≡ dist y myN.zero := myEq_symm (dist_commutative _ _ • (dist_commutative _ _ • dist_from_zero y))
            )
          )


      | mySum.inr hyx =>
          mySum.inl (
            calc
              myAdd (dist x y) (dist y myN.zero) ≡ myAdd (dist x y) y := ap (fun t => myAdd (dist x y) t) _ _ (dist_commutative y myN.zero • (dist_commutative _ _ • dist_from_zero y))
              _ ≡ myAdd (dist y x) y := ap (fun t => myAdd t y) _ _ (dist_symm x y)
              _ ≡ x := myAdd_commutative _ _ •  add_dist_of_leq y x hyx
              _ ≡ dist x myN.zero := myEq_symm (dist_commutative _ _ • (dist_commutative _ _ • dist_from_zero x))
          )

  | myN.succ x, myN.succ y, myN.succ z =>
      dist_transitivity x y z



-- Additional porpositions about less-than

def less_than_irrefl (n : myN) (p : less_than n n) : Empty :=
  match n with
  | myN.zero => p
  | myN.succ n' => (less_than_irrefl n') p

def less_than_on_equals (m n : myN) (p : m ≡ n) (q : less_than m n) : Empty :=
  match n with
  | myN.zero =>
    match m with
    | myN.zero => q
    | myN.succ _ => q

  | myN.succ n' =>
    match m with
    | myN.zero => Empty.elim (P8 n' p)
    | myN.succ m' => less_than_on_equals m' n' (Equality_Equiv_conv (Equality_Equiv m'.succ n'.succ p)) q
