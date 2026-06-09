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

def Equality_Equiv_conv (m n : N) (p : Eq_N m n) : m ≡ n :=
  match m, n with
  | N.zero, N.zero => MyEq.refl _
  | N.zero, N.succ _ => Empty.elim p
  | N.succ _, N.zero => Empty.elim p
  | N.succ m, N.succ n => ap N.succ _ _ (Equality_Equiv_conv m n p)   -- (Eq_N m n) = (Eq_N m.succ n.succ)


-- Theorem 6.4.1
-- Peano's seventh axiom (m ≡ n  ↔  m+1 ≡ n+1)

def P7 (m n : N) (p : m ≡ n) : m.succ ≡ n.succ :=
  Equality_Equiv_conv m.succ n.succ (Equality_Equiv m n p)    -- (m ≡ n) → (Eq_N m n) = (Eq_N m+1 n+1) → m+1 ≡ n+1

def P7_conv (m n : N) (p : m.succ ≡ n.succ) : m ≡ n :=
  Equality_Equiv_conv m n (Equality_Equiv m.succ n.succ p)


-- Theorem 6.4.2
-- Peano's eight axiom (0 ≠ n+1)

def P8 (n : N) (p : N.zero ≡ n.succ) : Empty :=
  Equality_Equiv N.zero n.succ p
