import HoTTRijke.Inductive_Int
import HoTTRijke.chapter5_eq

open chapter5_myeq

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
def add_succ_to_equals (k : N) (p : m ≡ n) :  (m × (N.succ k)) ≡ (n × (N.succ k)) :=
  ap (fun x : N => x × (N.succ k)) _ _ p

def add_succ_injective (p : (m × (N.succ k)) ≡ (n × (N.succ k))) : m ≡ n :=
  match k with
  | N.zero => p
  | N.succ k' => sorry
