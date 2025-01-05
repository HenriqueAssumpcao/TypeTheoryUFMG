/-
  Exercise 10.2 of Nederpelt and Geuvers.
  Code by Csaba.
-/

/-
  A ‘contradiction’ is formalised in λD as being an inhabitant of ⊥.

  (a) Show that the following primitive definition causes inconsistency,
  because it enables the derivation of a contradiction in λD:

  A, B : *ₚ ▸ k(A, B) := ⫫ : (A ⇒ B) ⇒ A.
-/

-- we define a term k(A,B) : (A → B) → A
axiom k (A B : Prop): (A → B) → A

-- now we prove False using k
theorem FalseIsTrue : False := by
  have h : (False → False) → False := k False False
  have h1 : (False → False) := False.elim
  exact h h1

/-
  (b) Show that the following pair of primitive definitions causes
  inconsistency:
    ∅ ▸ ιDN := ⫫ : ∀A : ∗ₚ. (¬¬A ⇒ A)
    ∅ ▸ neg-imp := ⫫ : ∀A : ∗ₚ. (A ⇒ ¬A)
-/


/-
  To solve this exercise, I'll recreate constructive logic from scratch so that
  I can be sure that the solution does not accidentally use the principle of the
  excluded middle.

  Let us define False (⊥) and negation as on page 138 of
  [NG].
-/

def myFalse : Prop := ∀A : Prop, A
def myNeg (A : Prop) := A → myFalse


-- Let us define myOr and its introduction rules
def myOr (A B : Prop) : Prop := ∀C : Prop, (A → C) → (B → C) → C

theorem myOr_intro_left (A : Prop) (B : Prop) (At : A) : myOr A B := by
  intro C AC BC
  exact AC At

theorem myOr_intro_right (A : Prop) (B : Prop) (Bt : B) : myOr A B := by
  intro C AC BC
  exact BC Bt


-- In these terms the axioms look like this:
axiom ιDN (A : Prop): (myNeg (myNeg A)) → A
-- ((A → ⊥) → ⊥) → A

axiom neg_imp (A : Prop) : A → myNeg A
-- A → (A → ⊥)

-- We'll need the contrapositive of neg_imp
theorem neg_imp_rev (A : Prop) : myNeg A → A := by
  intro nA
  apply ιDN A
  apply neg_imp
  exact nA

/-
  The ιDN axiom implies ιET (excluded third or excluded middle)
  This was surprisingly hard to prove, I used ideas from
  https://proofassistants.stackexchange.com/q/1856
-/

theorem ιET (A: Prop) : myOr A (myNeg A) := by
  have h1 : myNeg (myOr A (myNeg A)) →  myNeg A  := by
    intro h
    exact fun (hA : A) => h (myOr_intro_left A  (myNeg A) (hA))

  have h2 : myNeg (myOr A (myNeg A)) → myFalse := by
    intro h
    exact h (myOr_intro_right A (myNeg A) (h1 h))

  exact ιDN (myOr A (myNeg A)) h2

/-
  We prove False from these axioms.
-/

theorem myFalseIsTrue : myFalse := by
  intro A

  apply ιET A
  exact fun x => x
  exact neg_imp_rev A

/-
  (c) Show that the following definition, resembling the induction axiom,
  causes inconsistency:
  P : ℕ → ∗ₚ ▸ ind-s(P) := ∀n : ℕ. (P n ⇒ P (s n)) ⇒ ∀n : ℕ. P n.
-/

axiom ind_s (P : Nat → Prop) : ∀n : Nat, (P n → P (Nat.succ n)) → ∀n : Nat, P n

/-
  The problem with this axiom is that there is no starting point for the induction. One must also
  assume that the proposition P is true for 0 in order to state that P is true for all n : Nat.

  We use this erroneous axiom to show that all natural numbers are greater than one.
-/

def bigger_than_one (a : Nat) := a > 1

/-
  Theorem: If a is a natural, than a > 1.
-/

theorem all_naturals_are_bigger_than_one : ∀a : Nat, bigger_than_one a := by
  have h : ∀n : Nat, bigger_than_one n → bigger_than_one (Nat.succ n) := by
    intro n hn
    unfold bigger_than_one at *
    apply Nat.lt_trans hn
    exact Nat.lt_succ_self n

  intro a
  exact ind_s bigger_than_one a (h a) a

-- second solution suggested by https://wsinrpn.win.tue.nl/CUP-C-Selected-exercises.pdf

theorem NaturalsImplyFalse : ∀a : Nat, False := by
  apply ind_s
  trivial
  exact 0

theorem FalseIsTrue2 : False := by
  apply NaturalsImplyFalse
  exact 0
