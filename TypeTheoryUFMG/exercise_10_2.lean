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

#check k

-- now we prove False using k
example : False := by
  have h : (False → False) → False := k False False
  have h1 : (False → False) := False.elim
  exact h h1

/-
  (b) Show that the following pair of primitive deﬁnitions causes
  inconsistency:
    ∅ ▸ ιDN := ⫫ : ∀A : ∗ₚ. (¬¬A ⇒ A)
    ∅ ▸ neg-imp := ⫫ : ∀A : ∗ₚ. (A ⇒ ¬A)
-/


/-
  (c) Show that the following deﬁnition, resembling the induction axiom,
  causes inconsistency:
  P : ℕ → ∗ₚ ▸ ind-s(P) := ∀n : ℕ. (P n ⇒ P (s n)) ⇒ ∀n : ℕ. P n.
-/
