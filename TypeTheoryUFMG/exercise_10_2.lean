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

-- we define a term k(A, B) : (A → B) → A
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

  Let us define False (⊥) and negation as on page 138 of [NG].
-/

def myFalse : Prop := ∀A : Prop, A

def myNeg (A : Prop) := A → myFalse


-- Let us define myOr and its introduction rules
def myOr (A B : Prop) : Prop := ∀C : Prop, (A → C) → ((B → C) → C)

theorem myOr_intro_left (A B : Prop) (At : A) : myOr A B := by
  intro C AC BC
  -- C : Prop, AC : A → C, BC : B → C
  exact AC At

theorem myOr_intro_right (A B : Prop) (Bt : B) : myOr A B := by
  intro C AC BC
  -- C : Prop, AC : A → C, BC : B → C
  exact BC Bt


-- In these terms the axioms look like this:
axiom ιDN (A : Prop): (myNeg (myNeg A)) → A
-- ((A → ⊥) → ⊥) → A

axiom neg_imp (A : Prop) : A → myNeg A
-- A → (A → ⊥)

-- We'll need the contrapositive of neg_imp
theorem neg_imp_rev (A : Prop) : myNeg A → A := by
  intro nA        -- nA : myNeg A ≅ A → myFalse
  -- target is: A
  apply ιDN A
  -- target is myNeg (myNeg A)
  apply neg_imp
  -- target is myNeg A
  exact nA

/-
  The ιDN axiom implies ιET (excluded third or excluded middle)
  This was surprisingly hard to prove, First, I used ideas from
  https://proofassistants.stackexchange.com/q/1856. Then, in the seminar,
  Bernardo realized that ¬¬(P ∨ ¬P) is true also in constructive logic.
  This approach gives a more elegant solution.
-/

theorem not_not_p_or_not_p : ∀P : Prop, myNeg (myNeg (myOr P  (myNeg P))) := by
  intro P X
  have Y : myNeg P := λ hp : P => X (myOr_intro_left P (myNeg P) hp)
  have Z : myOr P (myNeg P) := myOr_intro_right P (myNeg P) Y
  exact X Z

theorem p_or_not_p : ∀P : Prop, myOr P (myNeg P) := by
  intro P
  apply ιDN
  exact not_not_p_or_not_p P


theorem ιET (A: Prop) : myOr A (myNeg A) := by
  apply ιDN
  exact neg_neg_p_or_neg_p A


/-
  We prove False from these axioms.
-/

theorem myFalseIsTrue : myFalse := by
  intro A
  -- A : Prop
  -- target is A
  apply ιET A
  -- now need to prove that A → A and myNeg A → A
  -- the first is an identity function
  exact fun x => x
  -- the second is neg_imp_rev
  exact neg_imp_rev A

/-
  (c) Show that the following definition, resembling the induction axiom,
  causes inconsistency:
  P : ℕ → ∗ₚ ▸ ind-s(P) := ∀n : ℕ. (P n ⇒ P (s n)) ⇒ ∀n : ℕ. P n.
-/

axiom ind_s (P : Nat → Prop) : (∀n : Nat, (P n → P (Nat.succ n))) → (∀n : Nat, P n)
-- ind_s (P : Nat → Prop) (n : Nat) : (P n → P n.succ) → ∀ (n✝ : Nat), P n✝

/-
  The problem with this axiom is that there is no starting point for the induction. One must also
  assume that the proposition P is true for 0 in order to state that P is true for all n : Nat.

  We use this erroneous axiom to show that all natural numbers are greater than one.
-/

def bigger_than_one (a : Nat) : Prop := a > 1

/-
  Theorem: If a is a natural, then a > 1.
-/

theorem all_naturals_are_bigger_than_one : ∀a : Nat, bigger_than_one a := by

  -- aux statement to show that if n is bigger than one, then succ n is also
  have h : ∀n : Nat, bigger_than_one n → bigger_than_one (Nat.succ n) := by
    intro n hn
    -- n : Nat, hn : bigger_than_one n
    -- target is bigger_than_one n.succ
    unfold bigger_than_one
    -- target is now n.succ > 1
    apply Nat.lt_trans hn
    -- target now is n < n.succ
    exact Nat.lt_succ_self n
  apply ind_s
  exact h

-- second solution suggested by https://wsinrpn.win.tue.nl/CUP-C-Selected-exercises.pdf

theorem NaturalsImplyFalse : ∀_ : Nat, False := by

  apply ind_s
  -- target now: False → False and Nat
  -- First target: False → False
  intro a F
  -- F : False
  exact F

theorem FalseIsTrue2 : False := by
  apply NaturalsImplyFalse
  exact 0
