-- code by @bernborgess

namespace Chapter7
-- 7.3 An example of propositional logic in λC

def FALSE := ∀ A : Prop, A
def NOT (A : Prop) := A → FALSE
def AND (A B : Prop) := ∀ C : Prop, (A → B → C) → C
def OR (A B : Prop) := ∀ C : Prop, (A → C) → (B → C) → C

example : (A ∨ B) → (¬A → B) :=
  λ aorb =>
  Or.elim aorb
  (λ ha hna => absurd ha hna)
  (λ hb _hna => hb)

example : (OR A B) → (NOT A → B) :=
  λ (x : OR A B) (y : NOT A) =>
  have xB : (A → B) → (B → B) → B := x B
  have fu : A → B := λ u : A ↦ (y u B)
  have xBfu : (B → B) → B := xB fu
  have fv : B → B := λ v ↦ v
  show B from xBfu fv

-- 7.4 Classical logic in λC
theorem not_iff_NOT {A : Prop} : (NOT A) ↔ ¬A := by
  constructor
  . intro na a
    apply na a
  . intro na a
    exact absurd a na

theorem and_iff_AND {A B : Prop} : AND A B ↔ A ∧ B := by
  constructor
  . intro andab
    apply andab
    intro a b
    constructor
    . exact a
    . exact b
  . intro ⟨a,b⟩ C f
    exact f a b

theorem or_iff_OR {A B : Prop} :
  OR A B ↔ A ∨ B := by
  constructor
  . intro fab
    apply fab (A ∨ B)
    . intro a
      exact show A ∨ B from Or.inl a
    . intro b
      exact show A ∨ B from Or.inr b
  . intro aorb C a2c b2c
    apply Or.elim aorb
    . intro a
      exact a2c a
    . intro b
      exact b2c b

-- Constructive Logic + Excluded Third implies Double Negation
theorem et_implies_dn
  (iET : ∀ α : Prop, α ∨ (NOT α))
  : ∀ β : Prop, NOT (NOT β) → β := by
  intro β x
  have bnb : β ∨ (NOT β) := iET β
  rw [←or_iff_OR] at bnb
  unfold OR at bnb
  -- bnb : ∀ (C : Prop), (β → C) → (¬β → C) → C
  apply bnb β id
  intro z
  exact x z β

-- 7.5 Predicate logic in λC
def EXISTS (S : Type) (P : S → Prop) :=
  ∀ α : Prop, ((∀ x : S, (P x → α)) → α)

def Nat.Even (n : Nat) := n % 2 = 0
#check Nat.Even
#check EXISTS Nat Nat.Even

example : EXISTS Nat Nat.Even := by
  intro α fa
  apply fa 2
  rfl

#check Exists.intro

theorem exists_iff_EXISTS {α : Type} {p : α → Prop}
  : (∃ w, p w) ↔ EXISTS α p := by
  constructor
  . intro ⟨w,pw⟩ β fa
    apply fa w
    exact pw
  . intro ex
    apply ex
    intro x px
    exact ⟨x,px⟩

theorem not_exists_imp_forall_not {S : Type} {P : S → Prop}
  : ¬(∃x:S,P x) → (∀y:S,¬(P y)) := by
  intro u y v
  apply u
  rw [exists_iff_EXISTS]
  intro α w
  exact w y v

-- Exercises
-- 7.1 Verify that each of the following expressions is a tautology in constructive
-- logic, (1) by giving a proof in natural deduction, and (2) by giving a
-- corresponding derivation in λC.
-- (For the natural deduction rules concerning ⇒, ⊥ and ¬, see Sec-
-- tion 7.1.)
-- You may employ the flag style for the derivations, as in the examples
-- given in the present chapter.

variable {A B : Prop}
-- (a) B ⇒ (A ⇒ B),
example : B → (A → B) := by
    intro b _a
    exact b

example : B → (A → B) :=
    λ b _a => b

-- (b) ¬A ⇒ (A ⇒ B),
example : ¬A → (A → B) := by
    intro na a
    contradiction

example : ¬A → (A → B) :=
    λ na a =>
    False.elim (na a)

-- (c) (A ⇒ ¬B) ⇒ ((A ⇒ B) ⇒ ¬A),

-- (d) ¬(A ⇒ B) ⇒ ¬B (hint: use part (a)).
example : ¬(A → B) → ¬B :=
    λ p q =>
    have np : A → B := λ _ => q
    absurd np p

-- 7.2 (a) Formulate the double negation law (DN) as an axiom in λC.
-- (b) Verify that the following expression is a tautology in classical logic,
-- by giving a corresponding flag-style derivation in λC (use DN):
-- (¬A ⇒ A) ⇒ A
example (DN : ∀ α : Prop, ¬¬α → α)
    : (¬A → A) → A :=
    λ p =>
    have nnnaf : ¬¬¬A → False:= λ x : ¬¬¬A =>
        have na : ¬A := DN (¬A) x
        have a : A := p (DN (¬A) x)
        absurd a na
    sorry


example (DN : ∀ α : Prop, ¬¬α → α)
    : (¬A → A) → A := by
    intro a
    apply DN A
    intro na
    exact absurd (a na) na

example (DN : ∀ α : Prop, ¬¬α → α)
    : (¬A → A) → A :=
    λ a =>
    DN A (λ na =>
            absurd (a na) na)

-- 7.3 Give λC-derivations proving that the following expressions are tautologies
-- in classical logic (so you may use DN or ET):
-- (a) (A ⇒ B) ⇒ (¬B ⇒ ¬A),
example (EM : ∀ α : Prop, α ∨ ¬α)
    : (A → B) → (¬B → ¬A) :=
    λ a2b nb =>
    Or.elim (EM A)
        (λ a => absurd (a2b a) nb)
        (λ na => na)

example : (A → B) → (¬B → ¬A) :=
    λ a2b nb a => nb (a2b a)

-- (b) (¬B ⇒ ¬A) ⇒ (A ⇒ B)
example (EM : ∀ α : Prop, α ∨ ¬α)
    : (¬B → ¬A) → (A → B) :=
    λ nb2na a =>
    Or.elim (EM B)
    (λ b => b)
    (λ nb => absurd a (nb2na nb))

example (DN : ∀ α : Prop, ¬¬α → α)
    : (¬B → ¬A) → (A → B) :=
    λ nb2na a =>
    have y : ¬¬A → ¬¬B := (λ z nb a => nb (z a)) nb2na
    have nna : ¬¬A := (λ a na => na a) a
    have nnb : ¬¬B := y nna
    DN B nnb

-- 7.5 As Exercise 7.2 (b):
-- (a) ¬(A ⇒ B) ⇒ A (hint: use Exercise 7.1 (b)),
example (DN : ∀ α : Prop, ¬¬α → α)
    : ¬(A → B) → A :=
    λ x =>
    have h : ¬¬A := λ y => x (λ a => absurd a y)
    DN A h

-- (b) ¬(A ⇒ B) ⇒ (A ∧ ¬B) (hint: use Exercise 7.1 (d)).
example (DN : ∀ α : Prop, ¬¬α → α)
    : ¬(A → B) → (A ∧ ¬B) :=
    λ x =>
    have a : A := (λ v => DN A (λ y => v (λa => absurd a y))) x
    have nb : ¬B := (λ p q => absurd (λ _ => q) p) x
    ⟨a,nb⟩

example : ¬(A → B) → ¬B :=
    λ p q =>
    have np : A → B := λ _ => q
    absurd np p

-- 7.7 Give λC-derivations to show that the following natural deduction rules
-- are derivable in λC:
-- (a) (∨-intro-left-sec),
example : A → OR A B :=
    λ x _C z _u => z x

-- (b) (∨-intro-right-sec)
example : B → OR A B :=
    λ x _C _z u => u x

-- 7.9 Verify that each of the following expressions is a tautology in constructive
-- logic, (1) by giving a proof in first order natural deduction, and (2) by
-- giving a flag-style derivation in λC:
-- (a) ∀x∈S (¬P (x) ⇒ (P (x) ⇒ (Q(x) ∧ R(x)))),
variable {S : Type}
variable {P Q R : S → Prop}
example : ∀ x : S, (¬P x → (P x → (Q x ∧ R x))) :=
    λ _ npx px => absurd px npx

-- (b) ∀x∈S (P (x)) ⇒ ∀y∈S (P (y) ∨ Q(y)).
example : (∀ x : S, P x) → (∀ y: S, P y ∨ Q y) :=
    λ apx y => Or.inl (apx y)

-- Exercise 7.11
-- Let S : ∗ and P, Q : S → ∗. Let y : Πα : ∗ . ((Πx : S . (P x → α)) → α),
-- z : Πx : S . (P x → Q x) and x : S.

theorem ex7
  (S : Type)
  (P Q : S → Prop)
  (y : ∀α:Prop,((∀x:S,(P x → α)) → α))
  (z : ∀x:S,(P x → Q x))
  (x : S)
  : True
  := by
  -- (a) Find a correct type for y(Q x).
  have _a : (∀ y : S, P y → Q x) → Q x := y (Q x)

  -- (b) Why is the application y(Q x)z incorrect?
  -- have b := y (Q x) z
  --   application type mismatch
  --   y (Q x) z
  -- argument
  --   z
  -- has type
  --   ∀ (x : S), P x → Q x : Prop
  -- but is expected to have type
  --   ∀ (x_1 : S), P x_1 → Q x : Prop Lean 4
  --  > Because z binds the same x for both predicates `P x` and `Q x`

  -- (c) Check that this results corresponds with Remark 7.5.2
  -- Remark 7.5.2 In the derivation it is essential that x ∈ FV (A), because
  -- otherwise the application in line (2) would be illegal (see Exercise 7.11).

  trivial


end Chapter7
