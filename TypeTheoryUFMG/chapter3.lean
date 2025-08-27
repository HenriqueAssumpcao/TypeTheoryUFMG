variable (nat bool : Type)

/-
  Exercises for chapter 3 of the book 'Type Theory and Formal Proof' by
  Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/


/- Exercise 3.2

Give a full (i.e. not-shortened) derivation in λ2 to show that the following
term is legal; use the ﬂag format.

M ≡λα,β,γ:∗. λf:α →β. λg:β →γ. λx:α. g(fx)

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
def M (α β γ : Type) (f : α → β) (g : β → γ) (x : α) := g (f x)
-- solution for (a)
variable (suc : nat → nat) (even : nat → bool)
def term_3_3_a := M nat nat bool suc even

-- solution for (b)

--(1)
-- applying β-reduction we conclude that the term_3_3_a is exactally λx : nat . even(suc x), so it is legal.

--(2)

def term_3_3_b := λ(x : nat) => even (suc x)

-- ################################################################

end ex_33
/-
Exercise 3.4
Give a shortened derivation in λ2 to show that the following term is legal in the context Γ ≡ nat : ∗, bool : ∗ :
  (λα, β : ∗. λf : α → α. λg : α → β. λx : α. g(f(fx))) nat bool.
-/

-- solution
namespace ex_34
def term_3_4 := (λ(α β : Type) => λ(f : α → α) => λ(g : α → β) => λ(x : α) => g (f (f x))) nat bool

end ex_34

/-
Exercise 3.5
Let ⊥ ≡ Πα : ∗ . α and Γ ≡ β : ∗, x : ⊥.

(a) Prove that ⊥ is legal.
(b) Find an inhabitant of β in context Γ.
(c) Give three not β-convertible inhabitants of β → β in context Γ, each
in β-normal form.
(d) Prove that the following terms inhabit the same type in context Γ:
λf : β → β → β . f (x β)(x β), x((β → β → β) → β)-/

namespace ex_35
variable(x:Q) (β: Prop)

-- solution for (a)
def  Q :=  ∀ A : Prop, A
example : Prop := Q


-- solution for (b)

example : β := x β

-- solution for (c)

example : β → β := x (β → β)
example : β → β := λ(y : β) => y
example : β → β := λ(y : β) => x (β → β) y

def term1 := λ(f : β → β → β) => f (x β) (x β)
def term2 := x ((β → β → β) → β)

example : (β → β → β) → β := term1
