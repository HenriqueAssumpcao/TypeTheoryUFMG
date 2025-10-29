/-
  Exercises for chapter 5 of the book 'Type Theory and Formal Proof' by
  Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/

/-
Exercise 5.2 Give a complete (i.e. unshortened) λP-derivation of
S : ∗ ⊢ S → S → ∗ : □,
  (a) in tree format,
  (b) in flag format.
-/

-- Solution
section

variable (S : Type)
#check (S → S → Type : Type 1)

-- Type ≡ ⋆  ;  Type 1 ≡ □

end

/-
Exercise 5.3
Extend the flag derivation of Exercise 5.2(b) to a complete derivation of
S : ∗, Q : S → S → ∗ ⊢ Πx : S. Πy : S. Qxy : ∗.
-/

-- Solution
section

variable (S : Type) (Q : S → S → Type)
#check (∀x : S, ∀y : S, Q x y : Type)

end


/-
xercise 5.5
Prove that A ⇒ ((A ⇒ B) ⇒ B) is a tautology by giving a shortened
λP-derivation.
-/

-- Solution
namespace ex_55

theorem T (A B : Prop) : A → ((A → B) → B) := by
  intro t
  intro h
  exact h t

end ex_55


/-
Exercise 5.6
Prove that (A ⇒ (A ⇒ B)) ⇒ (A ⇒ B) is a tautology, (first) in natural
deduction and (second) by means of a shortened λP-derivation.
-/

-- Solution
namespace ex_56

theorem T (A B : Prop) : (A → (A → B)) → (A → B) := by
  intro h
  intro h1
  have h2 := h h1
  have h3 := h2 h1
  exact h3

end ex_56


/-
Exercise 5.7
Prove that the following propositions are tautologies by giving shortened
λP-derivations:
  (a) (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)),
  (b) ((A ⇒ B) ⇒ A) ⇒ ((A ⇒ B) ⇒ B),
  (c) (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)).
-/

-- Solution for (a)
namespace ex_57a

theorem T (A B C : Prop) : (A → B) → ((B → C) → (A → C)) := by
  intro h
  intro h1
  intro h2
  have h3 := h h2
  have h4 := h1 h3
  exact h4

end ex_57a

-- Solution for (b)
namespace ex_57b

theorem T (A B : Prop) : ((A → B) → A) → ((A → B) → B) := by
  intro h
  intro h1
  have h2 := h h1
  have h3 := h1 h2
  exact h3

end ex_57b

-- Solution for (c)
namespace ex_57c

theorem T (A B C : Prop) : (A → (B → C)) → ((A → B) → (A → C)) := by
  intro h
  intro h1
  intro a
  have b := h1 a
  have h2 := h a
  have c := h2 b
  exact c

end ex_57c
