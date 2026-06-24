import HoTTRijke.Inductive_Int
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter3
import HoTTRijke.chapter4

open chapter5_myeq
open chapter3_booleans
open chapter4_coproducts
open chapter4_booleans

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


-- c)

-- 𝑚 ≠ 𝑚 + (𝑛 + 1)
def add_dont_fix (p : m ≡ myAdd m (N.succ n)) : Empty :=
  match m with
  | N.zero => Empty.elim (P8 _ (p • (left_zero_add_N n.succ))) -- 0 = 0 + (n+1) = n+1
  | N.succ m =>
    -- m+1 = (m+1) + (n+1) = (n+1) + (m+1) = ((n+1) + m) + 1 → m = (n+1) + m = m + (n+1) → ∅
    have h : m.succ ≡ (myAdd (n.succ) m).succ := p • (add_commutative _ _)
    have h1 : m ≡ myAdd m n.succ :=
      (Equality_Equiv_conv (Equality_Equiv m.succ ((myAdd (n.succ) m).succ) h)) • (add_commutative _ _)

    Empty.elim (add_dont_fix h1)

-- 𝑚 + 1 ≠ (𝑚 + 1)(𝑛 + 2)
def mult_dont_fix (p : (N.succ m) ≡ (N.succ m) × (N.succ (N.succ n))) : Empty :=
  match m  with
  | N.zero =>
    -- 0+1 = (0+1)·((n+1)+1) = (0+1) + (0+1)(n+1) = (0+1)(n+1) + (0+1) = (0+1)(n+1) + 1 → 0 = (0+1)(n+1) → (0+1) = 0 ou (n+1) = 0
    have h : N.zero.succ ≡ (N.zero.succ × n.succ).succ := p • (add_commutative _ _)
    have h1 : N.zero ≡ N.zero.succ × n.succ := Equality_Equiv_conv (Equality_Equiv N.zero.succ _ h)
    have h2 := mult_equals_zero (myEq_symm h1)
    match h2 with
    | mySum.inl k => Empty.elim (Equality_Equiv _ _ k)
    | mySum.inr k => Empty.elim (Equality_Equiv _ _ k)

  | N.succ m =>
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

def leq (m n : N) : Type :=
  match m, n with
  | N.zero, _ => Unit
  | N.succ _, N.zero => Empty
  | N.succ m, N.succ n => leq m n

-- a)

def leq_refl (n : N) : leq n n :=
  match n with
  | N.zero => ()
  | N.succ n => leq_refl n

def leq_antisymm (m n : N) (p : leq m n) (q : leq n m) : m ≡ n :=
  match m, n with
  | N.zero, N.zero => MyEq.refl _
  | N.zero, N.succ _ => Empty.elim q
  | N.succ _, N.zero => Empty.elim p
  | N.succ m, N.succ n => ap N.succ _ _ (leq_antisymm m n p q)

def leq_trans (m n k : N) (p : leq m n) (q : leq n k) : leq m k :=
  match m, n, k with
  | N.zero, _, _ => ()
  | N.succ _, N.zero, _ => Empty.elim p
  | N.succ _, N.succ _, N.zero => Empty.elim q
  | N.succ m, N.succ n, N.succ k => leq_trans m n k p q


--b)

def leq_total (m n : N) : mySum (leq m n) (leq n m) :=
  match m, n with
  | N.zero, _ => mySum.inl ()
  | N.succ _, N.zero => mySum.inr ()
  | N.succ m, N.succ n =>
    match leq_total m n with
    | mySum.inl p => mySum.inl p
    | mySum.inr q => mySum.inr q


-- c)

def add_leq (m n k : N) (p : leq m n) : leq (myAdd m k) (myAdd n k) :=
  match k with
  | N.zero => p
  | N.succ k => add_leq m n k p

def add_leq_conv (m n k : N) (p : leq (myAdd m k) (myAdd n k)) : leq m n :=
  match k with
  | N.zero => p
  | N.succ k => add_leq_conv m n k p


-- d)

def leq_equals (m n : N) (p : m ≡ n) : leq m n :=
  match m, n with
  | N.zero, N.zero => ()
  | N.zero, N.succ _ => Empty.elim (Equality_Equiv _ _ p)
  | N.succ _, N.zero => Empty.elim (Equality_Equiv _ _ (myEq_symm p))
  | N.succ m, N.succ n => leq_equals m n (Equality_Equiv_conv (Equality_Equiv m.succ n.succ p))

def mult_succ_leq (m n k : N) (p : leq m n) : leq (m × k) (n × k) :=
  match k with
  | N.zero => ()
  | N.succ k =>
    -- m < n => mk < nk => mk + m < nk + m => m + mk < nk + m => m + mk < m + nk => m + mk < n + nk
    have h_comm_left : leq (myAdd m (m × k)) (myAdd (m × k) m) :=
      leq_equals _ _ (add_commutative _ _)

    have h_add_leq : leq (myAdd (m × k) m) (myAdd (n × k) m) :=
      add_leq _ _ m (mult_succ_leq m n k p)

    have h_left : leq (myAdd m (m × k)) (myAdd (n × k) m) :=      -- (m + mk ≤ mk + m) and (mk + m ≤ nk + m) => (m + mk ≤ nk + m)
      leq_trans _ _ _ h_comm_left h_add_leq

    have h_comm_right : leq (myAdd (n × k) m) (myAdd m (n × k)) :=
      leq_equals _ _ (add_commutative _ _)

    have h_middle : leq (myAdd m (m × k)) (myAdd m (n × k)) :=    -- (nk + m ≤ m + nk) and (m + mk ≤ nk + m) => (m + mk ≤ m + nk)
      leq_trans _ _ _ h_left h_comm_right

    have h_final : leq (myAdd m (n × k)) (myAdd n (n × k)) :=     -- (m < n) and (m + mk ≤ m + nk) => (m + mk ≤ n + nk)
      add_leq m n (n × k) p

    leq_trans _ _ _ h_middle h_final

def mult_succ_leq_conv (m n k : N) (p : leq (m × k.succ) (n × k.succ)) : leq m n :=
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

def leq_min (k m n : N) (p : leq k (N_min m n)) : myProd (leq k m) (leq k n) :=
  match k with
  | N.zero => myProd.mk () ()
  | N.succ k =>
    match m, n with
    | N.zero, n =>
    have h : (N_min N.zero n) ≡ N.zero :=
      match n with
      | N.zero => MyEq.refl _
      | N.succ _ => MyEq.refl _

    have h1 : leq k.succ N.zero := leq_trans k.succ (N_min N.zero n) N.zero p (leq_equals (N_min N.zero n) N.zero h)
    myProd.mk (leq_trans _ _ _ h1 ()) (leq_trans _ _ _ h1 ())

    | m, N.zero =>
    have h : (N_min m N.zero) ≡ N.zero :=
      match m with
      | N.zero => MyEq.refl _
      | N.succ _ => MyEq.refl _

    have h1 : leq k.succ N.zero := leq_trans k.succ (N_min m N.zero) N.zero p (leq_equals (N_min m N.zero) N.zero h)
    myProd.mk (leq_trans _ _ _ h1 ()) (leq_trans _ _ _ h1 ())

    | N.succ m, N.succ n =>
      let h := leq_min k m n p
      myProd.mk (proj1 h) (proj2 h)

def leq_zero (n : N) (p : leq n N.zero): n ≡ N.zero :=
  match n with
  | N.zero => MyEq.refl _
  | N.succ _ => Empty.elim p

def max_equals_zero (m n : N) (p : (N_max m n) ≡ N.zero) : myProd (m ≡ N.zero) (n ≡ N.zero) :=
  match m, n with
  | N.zero, N.zero => myProd.mk (MyEq.refl _) (MyEq.refl _)
  | N.zero, N.succ _ => Empty.elim (Equality_Equiv _ _ p)
  | N.succ _, N.zero => Empty.elim (Equality_Equiv _ _ p)
  | N.succ _, N.succ _ => Empty.elim (Equality_Equiv _ _ p)

def leq_max (k m n : N) (p : leq (N_max m n) k) : myProd (leq m k) (leq n k) :=
  match k with
  | N.zero =>
    have h1 : myProd (m ≡ N.zero) (n ≡ N.zero) := max_equals_zero m n (leq_zero (N_max m n) p)
    myProd.mk (leq_equals _ _ (proj1 h1)) (leq_equals _ _ (proj2 h1))

  | N.succ k =>
    match m, n with
    | N.zero, n =>
    have h1 : n ≡ N_max N.zero n :=
      match n with
      | N.zero => MyEq.refl _
      | N.succ _ => MyEq.refl _
    have h2 : leq n k.succ := leq_trans _ _ _ (leq_equals n (N_max N.zero n) h1) p
    myProd.mk () h2

    | m, N.zero =>
    have h1 : m ≡ N_max m N.zero :=
      match m with
      | N.zero => MyEq.refl _
      | N.succ _ => MyEq.refl _
    have h2 : leq m k.succ := leq_trans _ _ _ (leq_equals m (N_max m N.zero) h1) p
    myProd.mk h2 ()

    | N.succ m, N.succ n =>
      let h := leq_max k m n p
      myProd.mk (proj1 h) (proj2 h)
