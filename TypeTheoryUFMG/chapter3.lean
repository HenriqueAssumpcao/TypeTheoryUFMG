
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
section -- Section is used to define variables locally

variable (nat bool : Type) (suc : nat → nat) (even : nat → bool) -- this variables cannot be used outside this section

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
section

variable (α β : Prop) (x : α → ex_35.Q) (f : (α → α) → α)

-- inhabitant of α
example : α := f (λ y : α => y)

-- inhabitant of β
def a := f (λy : α => y)
example : β := x (a α f) β

end
end ex_37

/-
Exercise 3.8
Recall that K ≡ λ xy. x in untyped lambda calculus.
Consider the following types:
T1 ≡ Π α, β : ∗ . α → β → α and T2 ≡ Π α : ∗ . α → (Π β : ∗. β → α).
Find inhabitants t1 and t2 of T1 and T2, which may be considered as
different closed λ2-versions of K.
-/

-- solution
namespace ex_38

def T1 := ∀(α β : Type), α → β → α
def T2 := ∀(α : Type), α → (∀ (β : Type), β → α)

def M1 (α β : Type) (x : α) (_ : β) := x
def M2 (α : Type) (x : α) (β : Type) (_ : β) := x

#check (M1 : T1)
#check (M2 : T2)

/- M1 ≡ (λα,β : ∗ . λx : α. λy : β . x) and M2 ≡ (λα : ∗ . (λx : α. (λβ : ∗ . (λy : β . x))))
They are closed λ2-versions of k because in each of them we're adding types to the variables x and y of the untyped
term k ≡ (λxy. x) in such a way that there are no free type variables on it. -/

end ex_38


/-
Execise 3.9
Find a closed λ2-version of S ≡ λxyz. xz(yz), and establish its type.
-/

-- solution
namespace ex_39

def S2 (α β γ : Type) (x : α → (β → γ)) (y : α → β) (z : α) := x z (y z)
def T := ∀(α β γ : Type), (α → (β → γ)) →  (α → β) → (α) → γ

#check (S2 : T)

end ex_39

/-
Exercise 3.10
Let M ≡ λx : (Πα : ∗ . α → α) . x(σ → σ)(xσ).
  (a) Prove that M is legal in λ2.
  (b) Find a term N such that MN is legal in λ2 and may be considered
    to be a proper way of adding type information to (λx. xx)(λy. y).
-/


namespace ex_310
section

-- solution for (a)
def M {σ : Type} := λx : (∀ α : Type, α → α) => x (σ → σ) (x σ)
def T {σ : Type} := (∀α : Type, α → α) → σ → σ

#check (M : T)

/- Thus, in the context Γ ≡ σ : Type, M has type T. We have to add the context on definition of T because, in λ2, types must
have all free type variables declared. -/

-- solution for (b)
def N (α : Type) (x : α) := x
def T' {σ : Type} := σ → σ

#check (M N : T')

end
end ex_310

/-
Exercise 3.11
Take ⊥ as in Exercise 3.5. Prove that the following term is legal in the
empty context:
λx : ⊥ . x(⊥ → ⊥ → ⊥)(x(⊥ → ⊥)x)(x(⊥ → ⊥ → ⊥)xx).
What is its type?
-/

-- solution
namespace ex_311

def Q := ex_35.Q
def M (x : Q) := x (Q → Q → Q) (x (Q → Q) x) (x (Q → Q → Q) x x)


#check (M : Q → Q)

end ex_311

/-
Exercise 3.12
As mentioned in Section 3.8, we have in λ2 the polymorphic Church
numerals. They resemble the untyped Church numerals, as described in
Exercises 1.10 and 1.13(b). For example:
Nat ≡ Πα : ∗ . (α → α) → α → α,
Zero ≡ λα : ∗ . λf : α → α. λx : α. x, having type Nat,
One ≡ λα : ∗ . λf : α → α. λx : α. fx, with type Nat, as well,
Two ≡ λα : ∗ . λf : α → α. λx : α. f(fx).
We define Suc as follows as a λ2-term:
Suc ≡ λn : Nat. λβ : ∗ . λf : β → β. λx : β. f(nβfx).
Check that Suc acts as a successor function for the polymorphic Church
numerals, by proving that Suc Zero =β One and Suc One =β Two.
-/

-- Solution
namespace ex_312

def Nat := ∀ (α : Type), (α → α) → α → α
def Zero (α : Type) (_ : α → α) (x : α) := x
def One (α : Type) (f : α → α) (x : α) := f x
def Two (α : Type) (f : α → α) (x : α) := f (f x)
def Suc (n : Nat) (β : Type) (f : β → β) (x : β) := f (n β f x)

theorem T1 : Suc Zero = One := by
  rfl

theorem T2 : Suc One = Two := by
  rfl

end ex_312

/-
Exercise 3.13
See the previous exercise.
  (a) We define Add in λ2 as follows:
    Add ≡ λm,n : Nat. λα : ∗ . λf : α → α. λx : Nat. mαf(nαfx).
    Show that Add simulates addition, by evaluating Add One One
  (b) Find a λ2-term Mult that simulates multiplication on Nat.
-/

namespace ex_313
def Nat := ex_312.Nat
def One := ex_312.One
def Two := ex_312.Two

-- solution for (a)
def Add (m n : Nat) (α : Type) (f : α → α) (x : α) := m α f (n α f x)

theorem T : Add One One = Two := by
  rfl

-- solution for (b)

end ex_313
