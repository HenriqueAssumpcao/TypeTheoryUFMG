/-
  Exercises for chapter 4 of the book 'Type Theory and Formal Proof' by
  Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/

/-
Exercise 4.2
Give complete λω-derivations, first in tree format and then in flag format
(not shortened), of the following judgements:
  (a) ∅ ⊢ (∗ → ∗) → ∗ : □,
  (b) α : ∗, β: ∗ ⊢ (α → β) → α : ∗.
-/

-- Solution for (a)

example : Type 1 := (Type → Type) → Type

-- Solution for (b)
section
variable (α β : Type)

example : Type := (α → β) → α

end


/-
Exercise 4.3
  (a) Give a complete (i.e. not shortened) λω-derivation in flag format of
    α,β : ∗, x: α, y : α → β ⊢ yx:β.
  (b) Give a shortened λω-derivation in flag format of
    α,β : ∗, x: α, y : α → β, z:β → α ⊢ z(yx):α.
-/

-- Solution for (a)
section
variable (α β : Type) (x : α) (y : α → β)

example : β := y x

end

-- Solution for (b)
section
variable (α β : Type) (x : α) (y : α → β) (z : β → α)

example : α := z (y x)

end


/-
Example 4.4
Give shortened λω-derivations in flag format of the following judgements:
  (a) α : ∗, β: ∗ → ∗ ⊢ β(βα): ∗,
  (b) α : ∗, β: ∗ → ∗, x: β(βα) ⊢ λy: α. x : α → β(βα),
  (c) ∅ ⊢ λα: ∗ . λβ:∗ → ∗ . β(βα) : ∗ → (∗ → ∗) → ∗,
  (d) ∅ ⊢ (λα:∗. λβ:∗ → ∗. β(βα)) nat (λγ : ∗ . γ) : ∗, assuming that
    nat is a constant of type ∗.
-/

-- Solution for (a)
section
variable (α : Type) (β : Type → Type)

example : Type := β (β α)

end

-- Solution for (b)
section
variable (α : Type) (β : Type → Type) (x : β (β α))

example : α → β (β α) := λ_ : α => x

end

-- Solution for (c)

example : Type → (Type → Type) → Type := λα : Type => (λβ : Type → Type => β (β α))

-- Solution for (d)
section
variable (nat : Type)

example : Type :=(λα : Type => (λβ : Type → Type => β (β α))) nat (λγ : Type => γ)

end


/-
Exercise 4.5
Give a shortened λω-derivation in flag format of the following judgement:
α : ∗, x: α ⊢ λy:α. x : (λβ:∗. β → β)α.
-/

-- Solution
section
variable (α : Type) (x : α)

example : (λβ : Type => β → β) α := λ_ : α => x

end
