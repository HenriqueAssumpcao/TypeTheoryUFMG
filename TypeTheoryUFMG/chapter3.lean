
/-
  Exercises for chapter 3 of the book 'Type Theory and Formal Proof' by
  Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/


/- Exercise 3.2

Give a full (i.e. not-shortened) derivation in λ2 to show that the following
term is legal; use the ﬂag format.

M ≡ λ α,β,γ : ∗. λ f : α → β. λ g : β → γ. λ x : α. g(fx)

--/
namespace ex_32
def M (α β γ : Type) (f : α → β) (g : β → γ) (x : α) := g (f x)
example : ∀ (α β γ : Type), (α → β) →  (β → γ) → α → γ := M

end ex_32

/-Exercise 3.3
  Take M as in Exercise 3.2. Assume nat : ∗, bool : ∗, suc : nat → nat and even : nat → bool.
  (a) Prove that M nat nat bool suc even is legal.
  (b) Prove that λx : nat . even(suc x) is legal, in two ways:
    (1) using Exercise 3.3(a) and Subject Reduction;
    (2) directly.
-/

namespace ex_33
section

variable (nat bool : Type) (suc : nat → nat) (even : nat → bool)

def M (α β γ : Type) (f : α → β) (g : β → γ) (x : α) := g (f x)

-- solution for (a)
def term_3_3_a {nat bool : Type} {suc : nat → nat} {even : nat → bool} := M nat nat bool suc even

-- solution for (b)

--(1)
-- applying β-reduction we conclude that the term_3_3_a is exactally λx : nat . even(suc x), so it is legal.

--(2)

def term_3_3_b := λ(x : nat) => even (suc x)

-- ################################################################

end
end ex_33

/-
Exercise 3.4
Give a shortened derivation in λ2 to show that the following term is legal in the context Γ ≡ nat : ∗, bool : ∗ ;
  (λα, β : ∗. λf : α → α. λg : α → β. λx : α. g(f(fx))) nat bool.
-/

-- solution
namespace ex_34

def term_3_4 {nat bool : Type} := (λ(α β : Type) => λ(f : α → α) => λ(g : α → β) => λ(x : α) => g (f (f x))) nat bool

end ex_34


/-
Exercise 3.5
Let ⊥ ≡ Πα : ∗ . α and Γ ≡ β : ∗, x : ⊥.

(a) Prove that ⊥ is legal.
(b) Find an inhabitant of β in context Γ.
(c) Give three not β-convertible inhabitants of β → β in context Γ, each
in β-normal form.
(d) Prove that the following terms inhabit the same type in context Γ:
λf : β → β → β . f (x β)(x β), x((β → β → β) → β)
-/

namespace ex_35
section

variable(x : Q) (β : Prop)

-- solution for (a)
def  Q :=  ∀ A : Prop, A
example : Prop := Q


-- solution for (b)
example : β := x β

-- solution for (c)
example : β → β := x (β → β)
example : β → β := λ(y : β) => y
example : β → β := λ(y : β) => x (β → β) y

-- solution for (d)
def term1 := λ(f : β → β → β) => f (x β) (x β)
def term2 := x ((β → β → β) → β)

example : (β → β → β) → β := term1 x β          -- Apply term1 to x and β "makes" the context Γ. It is necessary because def makes a "global term" with empty context
example : (β → β → β) → β := term2 x β

end
end ex_35

/-
Exercise 3.6
Find terms in ΛT2 that are inhabitants of the following λ2-types, each in
the given context Γ:

a) Π α,β : ∗ . (nat → α) → (α → nat → β) → nat → β, where Γ ≡ nat : ∗.
b) Π δ : ∗ . ((α → γ) → δ) → (α → β) → (β → γ) → δ, where Γ ≡ α : ∗, β: ∗, γ: ∗.
c) Π α,β,γ : ∗ . (α → (β → α) → γ) → α → γ, in the empty context.
-/

namespace ex_36

-- solution for (a)
def a {nat : Type} (α β : Type) (f : nat → α) (g : α → nat → β) (n : nat) :=  g (f n) n
example : ∀ (α β : Type), (nat → α) → (α → nat → β) → nat → β := a

-- solution for (b)
def b {α β γ : Type} (δ : Type) (f : (α → γ) → δ) (g : α → β) (h : β → γ) := f (λ x : α => h (g x))
example : ∀ (δ : Type), ((α → γ) → δ) → (α → β) → (β → γ) → δ := b

-- solution for (c)
def c (α β γ : Type) (f : α → (β → α) → γ) (x : α) := (f x) (λ _ : β => x)
example : ∀ (α β γ : Type), (α → (β → α) → γ) → α → γ := c

end ex_36

/-
Exercise 3.7
Take ⊥ as in Exercise 3.5.
Let context Γ be α : ∗, β : ∗, x : α → ⊥, f : (α → α) → α.
Give a derivation to successively calculate an inhabitant of α and an
inhabitant of β, both in context Γ.
-/
namespace ex_37


variable (α β : Prop) (x : α → ex_35.Q) (f : (α → α) → α)

-- inhabitant of α
example : α := f (λ y : α => y)

-- inhabitant of β
def a := f (λ y : α => y)
example : β := x (a α f) β
