/-
  Exercise 10.2 of Nederpelt and Geuvers.

  A ‘contradiction’ is formalised in λD as being an inhabitant of ⊥.
-/

variable (A B : Prop)

/-
  (a) Show that the following primitive deﬁnition causes inconsistency,
  because it enables the derivation of a contradiction in λD:

  A, B : *ₚ ▸ k(A, B) := ⫫ : (A ⇒ B) ⇒ A.
-/

-- we define a term k(A,B) : (A → B) → A
axiom k : (A → B) → A

-- now we prove False using k
theorem FalseIsTrue : False := by
  have h : (False → False) → False := k False False
  have h1 : (False → False) := False.elim
  exact h h1

/-
  (b) Show that the following pair of primitive deﬁnitions causes
  inconsistency:
    ∅ ▸ ιDN := ⫫ : ∀A : ∗ₚ. (¬¬A ⇒ A)
    ∅ ▸ neg-imp := ⫫ : ∀A : ∗ₚ. (A ⇒ ¬A)
-/

axiom ιDN : ¬¬A → A
axiom neg_imp : A → ¬A

/-
  We prove False from these axioms.
-/

theorem FalseIsTrue2 : False := by
  have ht : True := trivial
  have h : True → ¬True := neg_imp True
  have nt : ¬True := h ht
  have hh : True ∧ ¬True → False := by
    intro h
    exact h.2 h.1
  exact hh ⟨ht, nt⟩

/-
  Problem: this solution does not explicitly use the ιDN axiom. I think it is implicit in
  the proposition that True ∧ ¬True → False.
-/

/-
  (c) Show that the following deﬁnition, resembling the induction axiom,
  causes inconsistency:
  P : ℕ → ∗ₚ ▸ ind-s(P) := ∀n : ℕ. (P n ⇒ P (s n)) ⇒ ∀n : ℕ. P n.
-/

axiom ind_s (P : Nat → Prop) : ∀n : Nat, (P n → P (Nat.succ n)) → ∀n : Nat, P n

/-
  The problem with this axiom is that there is no starting point for the induction. One must also
  assume that the proposition P is true for 0 in order to state that P is true for all n : Nat.

  We use this errounous axiom to show that all natural numbers are greated than one.
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
