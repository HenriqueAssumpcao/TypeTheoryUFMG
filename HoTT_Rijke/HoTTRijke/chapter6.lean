import HoTTRijke.Inductive_Int
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter3
import HoTTRijke.chapter4

open chapter5_myeq
open chapter3_booleans
open chapter4_coproducts

namespace chapter6_Universes

-- Observational Equality

def E_0 (n : N) : Type :=   -- (0 = n)
  match n with
  | N.zero => Unit
  | N.succ _ => Empty

def E_S (_ : N) (X : (N → Type)) (m : N) : Type :=    -- (S(n) = m)
  match m with
  | N.zero => Empty
  | N.succ m => X m


def Eq_N (n m : N): Type :=
  match n with
  | N.zero => E_0 m
  | N.succ n => E_S n (Eq_N n) m


-- Lemma 6.3.2
-- Eq_N is reflexive

def refl_Eq_N (n : N) : Eq_N n n :=
  match n with
  | N.zero => ()
  | N.succ n => refl_Eq_N n


-- Proposition 6.3.3
-- Eq_N is equivalent to MyEq

def Equality_Equiv (m n : N) (p : m ≡ n) : Eq_N m n :=
  let P := fun x : N => fun _ : m ≡ x => Eq_N m x
  ind_eq P (refl_Eq_N m) n p                              -- Using induction principle

def Equality_Equiv_conv (p : Eq_N m n) : m ≡ n :=
  match m, n with
  | N.zero, N.zero => MyEq.refl _
  | N.zero, N.succ _ => Empty.elim p
  | N.succ _, N.zero => Empty.elim p
  | N.succ _, N.succ _ => ap N.succ _ _ (Equality_Equiv_conv p)   -- (Eq_N m n) = (Eq_N m.succ n.succ)



-- Theorem 6.4.1
-- Peano's seventh axiom (m ≡ n  ↔  m+1 ≡ n+1)

def P7 (m n : N) (p : m ≡ n) : m.succ ≡ n.succ :=
  Equality_Equiv_conv (Equality_Equiv m n p)    -- (m ≡ n) → (Eq_N m n) = (Eq_N m+1 n+1) → m+1 ≡ n+1

def P7_conv (m n : N) (p : m.succ ≡ n.succ) : m ≡ n :=
  Equality_Equiv_conv (Equality_Equiv m.succ n.succ p)


-- Theorem 6.4.2
-- Peano's eight axiom (0 ≠ n+1)

def P8 (n : N) (p : N.zero ≡ n.succ) : Empty :=
  Equality_Equiv N.zero n.succ p





-- ######################## Exercises ############################ --


-- 6.1
-- a)

-- (𝑚 = 𝑛) ↔ (𝑚 + 𝑘 = 𝑛 + 𝑘)
def add_natural_to_equals (k : N) (p : m ≡ n) : (myAdd m k) ≡ (myAdd n k) :=
  match k with
  | N.zero => p
  | N.succ k => ap N.succ _ _ (add_natural_to_equals k p)

def add_nat_injective (p : (myAdd m k) ≡ (myAdd n k)) : m ≡ n :=
  match k with
  | N.zero => p
  | N.succ _ => add_nat_injective (P7_conv _ _ p)

-- (𝑚 = 𝑛) ↔ (𝑚 · (𝑘 + 1) = 𝑛 · (𝑘 + 1))
example (k : N) (p : m ≡ n) :  (m × (N.succ k)) ≡ (n × (N.succ k)) := ap (fun x : N => x × (N.succ k)) _ _ p

def mult_succ_injective (p : (m × (N.succ k)) ≡ (n × (N.succ k))) : m ≡ n :=
  match m, n with
  | N.zero, N.zero => MyEq.refl _
  | N.zero, N.succ n =>
    have p' : N.zero ≡ N.succ (myAdd (n × k.succ)  k) :=
      (myEq_symm (myMult_zero_left k.succ)) • p • (myMult_succ_left n k.succ)     -- 0 = 0·(k+1) = (n+1)(k+1) = n(k+1)+(k+1) = (n(k+1)+k)+1

    Empty.elim (Equality_Equiv _ _ p')                                            -- (0 = x+1) ≡ ∅

  | N.succ m, N.zero =>
    have p' : N.zero ≡ N.succ (myAdd (m × k.succ)  k) :=
      (myEq_symm (myMult_zero_left k.succ)) • (myEq_symm p) • (myMult_succ_left m k.succ)

    Empty.elim (Equality_Equiv _ _ p')

  | N.succ m, N.succ n =>
    have h : (k.succ × m.succ) ≡ (k.succ × n.succ) :=
      (myMult_comm k.succ m.succ) • p • (myMult_comm n.succ k.succ)               -- (k+1)(m+1) = (m+1)(k+1) = (n+1)(k+1) = (k+1)(n+1)
    have p' : myAdd (k.succ × m) k.succ ≡ myAdd (k.succ × n) k.succ :=
      (add_commutative _ _) • h • (add_commutative _ _)
    have h' : (m × k.succ) ≡ (n × k.succ) :=
      (myMult_comm m k.succ) • (add_nat_injective p') • (myMult_comm k.succ n)    -- m(k+1) = (k+1)m = (k+1)n = n(k+1)

    Equality_Equiv_conv (Equality_Equiv m n (mult_succ_injective h'))             -- (m = n) → (m+1 = n+1)


-- b)

-- 𝑚 + 𝑛 = 0 ↔ (𝑚 = 0) e (𝑛 = 0)
example (p : m ≡ N.zero) (q : n ≡ N.zero) : (myAdd m n) ≡ N.zero := (ap (myAdd m) _ _ q) • p

def sum_equals_zero (p : (myAdd m n) ≡ N.zero) : myProd (m ≡ N.zero) (n ≡ N.zero) :=
  match n with
  | N.zero => myProd.mk p (MyEq.refl _)
  | N.succ _ => Empty.elim (Equality_Equiv _ _ p)

-- 𝑚 · 𝑛 = 0  <=> (𝑚 = 0) ou (𝑛 = 0)
def mult_equals_zero (p : (m × n) ≡ N.zero) : mySum (m ≡ N.zero) (n ≡ N.zero) :=
  match n with
  | N.zero => mySum.inr (MyEq.refl _)
  | N.succ n =>
    have h : myAdd (m × n) m ≡ N.zero := (add_commutative _ _) • p    -- (m·n)+m = m+(m·n) =  m(n+1) = 0
    mySum.inl (proj2 (sum_equals_zero h))

def mult_by_zero (x : mySum (m ≡ N.zero) (n ≡ N.zero)) : (m × n) ≡ N.zero :=
  match x with
  | mySum.inl x => (ap (fun y : N => myMult y n) _ _ x) • (myMult_zero_left n)    -- (m = 0) => (m·n = 0·n = 0)
  | mySum.inr x => ap (myMult m) _ _ x

-- 𝑚·𝑛 = 1 <=> (𝑚 = 1) e (𝑛 = 1)
def mult_one_by_one (p : myProd (m ≡ N.zero.succ) (n ≡ N.zero.succ)) : (m × n) ≡ N.zero.succ :=
  calc
    -- m·n = m(0+1) = m + m·0 = m + 0 = m = 0 + 1 = 1
    (m × n) ≡ m := ap (myMult m) _ _ (proj2 p)
    _ ≡ N.zero.succ := proj1 p

def mult_equals_one (p : (m × n) ≡ N.zero.succ) : myProd (m ≡ N.zero.succ) (n ≡ N.zero.succ) :=
  match m, n with
  | _, N.zero => Empty.elim (Equality_Equiv _ _ p)
  | N.zero, _ => Empty.elim (Equality_Equiv _ _ ((myMult_comm _ _) • p))

  | N.succ m, N.succ n =>
    have h : (myAdd m (m.succ × n)).succ ≡  N.zero.succ := (myEq_symm (left_successor_law_add _ _)) • p
    have h1: myAdd m (m.succ × n) ≡ N.zero :=
      Equality_Equiv_conv (Equality_Equiv (myAdd m (m.succ × n)).succ N.zero.succ h)

    have h2 : mySum (m.succ ≡ N.zero) (n ≡ N.zero) := mult_equals_zero (proj2 (sum_equals_zero h1))

    have m0 : m ≡ N.zero := proj1 (sum_equals_zero h1)
    match h2 with
    | mySum.inr n0 =>
      myProd.mk (Equality_Equiv_conv (Equality_Equiv m N.zero m0))
      (Equality_Equiv_conv (Equality_Equiv n N.zero n0))

    | mySum.inl m1 => Empty.elim (Equality_Equiv _ _ m1)
