variable (nat bool : Type)

/-
  Exercises for chapter 3 of the book 'Type Theory and Formal Proof' by
  Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/

-- M ≡λα,β,γ:∗.λf : α →β.λg:β →γ.λx:α.g(fx)

/-Exercise 3.3
  Take M as in Exercise 3.2. Assume nat : ∗, bool : ∗, suc : nat → nat and even : nat → bool.
  (a) Prove that M nat nat bool suc even is legal.
  (b) Prove that λx : nat . even(suc x) is legal, in two ways:
    (1) using Exercise 3.3(a) and Subject Reduction;
    (2) directly.
-/

-- solution for (a)
variable (suc : nat → nat) (even : nat → bool)

def M := λ(α β γ : Type) => λ(f : α → β) => λ(g : β → γ) => λ(x : α) => g (f x)

def term_3_3_a := M nat nat bool suc even

-- solution for (b)

--(1)
-- apllying β-reduction we conclude that the term_3_3_a is exactally λx : nat . even(suc x), so it is legal.

--(2)
def term_3_3_b := λ(x : nat) => even (suc x)

-- ################################################################


/-Exercise 3.4
Give a shortened derivation in λ2 to show that the following term is legal in the context Γ ≡ nat : ∗, bool : ∗ :
  (λα, β : ∗. λf : α → α. λg : α → β. λx : α. g(f(fx))) nat bool.
-/

-- solution

def term_3_4 := (λ(α β : Type) => λ(f : α → α) => λ(g : α → β) => λ(x : α) => g (f (f x))) nat bool
