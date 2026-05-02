/-
  Exercises for chapter 6 of the book 'Type Theory and Formal Proof' by
  Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/

/-
Exercise 6.1
  (a) Give a complete derivation in tree format showing that ⊥ ≡ Πα : ∗ . α
    is legal in λC (cf. Exercise 3.5).
  (b) The same for ⊥ → ⊥.
  (c) To which systems of the λ-cube does ⊥ belong? And ⊥ → ⊥?
-/

-- Solution for (a)
def Cont := ∀α : Prop, α

-- Solution for (b)
def Cont_Cont := Cont → Cont

-- Solution for (c)
-- Sorry


/-
Exercise 6.2
Let Γ ≡ S : ∗, P : S → ∗, A : ∗.
Prove by means of a flag derivation that the following expression is
inhabited in λC with respect to Γ:
(Πx : S. (A → Px)) → A → Πy : S. Py.
(You may shorten the derivation, as explained in Section 4.5.)
-/

-- Solution
section
namespace ex_62

variable {S : Type} {P : S → Prop} {A : Type}

theorem T : (∀x : S, (A → P x)) → A → ∀y : S, P y := by
  intro h
  intro a
  have r := λ y : S => h y a
  exact r

-- Second Solution

def t := λ f : ∀x : S, (A → P x) => λa : A => λy : S => f y a
#check (t : (∀x : S, (A → P x)) → A → ∀y : S, P y)

end ex_62
end


/-
Exercise 6.3
Let J be the judgement:
S: ∗, P: S → ∗ ⊢ λx : S. (Px → ⊥) : S → ∗.
  (a) Give a shortened λC-derivation of J.
  (b) Determine the (s1,s2)-combinations corresponding to all Πs (or arrows)
    occurring in J. (For ⊥, see Exercise 6.1.)
  (c) Which is the ‘smallest’ system in the λ-cube to which J belongs?
-/

-- Solution for (a)
section
variable {S : Type} {P : S → Prop}

#check (λx : S => (P x → Cont) : S → Prop)

end

-- Solution for (b) and (c)
-- Sorry


/-
Exercise 6.4
Let Γ ≡ S : ∗, Q : S → S → ∗ and let M be the following expression:
M ≡ (Πx,y : S. (Qxy → Qyx → ⊥)) → Πz : S. (Qzz → ⊥).
  (a) Give a shortened derivation of Γ ⊢ M : ∗ and determine the smallest
    subsystem to which this judgement belongs.
  (b) Prove in λC that M is inhabited in context Γ. You may use a shortened
    derivation.
  (c) We may consider Q to be a relation on set S. Moreover, it is reasonable
    to see A → ⊥ as the negation ¬A of proposition A. (We shall explain
    this in Section 7.1.) How can M then be interpreted, if we also take
    Figure 5.2 into account? And what is a plausible interpretation of the
    inhabiting term you found in (b)?
-/

section
namespace ex_64
-- Solution for (a)
variable {S : Type} {Q : S → S → Prop}

def M := (∀x y : S, (Q x y → Q y x → Cont)) → ∀z : S, (Q z z → Cont)

#check (M : Prop)


-- Solution for (b)

theorem b : (∀x y : S, (Q x y → Q y x → Cont)) → ∀z : S, (Q z z → Cont) := by
  intro f z P
  exact f z z P P


-- Solution for (c)
-- Sorry

end ex_64
end


/-
Exercise 6.5
Let J be the following judgement:
S : ∗ ⊢ λQ : S → S → ∗. λx : S. Qxx : (S → S → ∗) → S → ∗.
  (a) Give a shortened derivation of J and determine the smallest subsystem
    to which J belongs.
  (b) We may consider the variable Q in J as expressing a relation on
    set S. How could you describe the subexpression λx : S. Qxx in this
    setting? And what is then the interpretation of the judgement J?
-/

section
namespace ex_65
-- Solution for (a)
variable {S : Type}

def a := λQ : S → S → Prop => λx : S => Q x x

#check (a : (S → S → Prop) → S → Prop)


-- Solution for (b)
-- Sorry

end ex_65
end


/-
Exercise 6.6
Let M ≡ λS : ∗. λP : S → ∗. λx : S. (Px → ⊥).
  (a) Which is the smallest system in the λ-cube in which M may occur?
  (b) Prove that M is legal and determine its type.
  (c) How could you interpret the constructor M, if A → ⊥ encodes ¬A?
-/

namespace ex_66
-- Solution for (a)
-- Sorry

-- Solution for (b)

def M := λS : Type => λP : S → Prop => λx : S => (P x → Cont)

#check (M : ∀S : Type, (S → Prop) → (S → Prop))


-- Solution for (c)
-- Sorry

end ex_66


/-
Exercise 6.7
Given Γ ≡ S : ∗, Q: S → S → ∗, we define in λC the expressions:
M1 ≡ λx,y : S. ΠR : S → S → ∗. ((Πz : S. Rzz) → Rxy),
M2 ≡ λx,y : S. ΠR : S → S → ∗. ((Πu,v : S. (Quv → Ruv)) → Rxy).
  (a) Give an inhabitant of Πa : S. M1aa and a shortened derivation
    proving your answer.
  (b) Give an inhabitant of Πa,b : S. (Qab → M2ab) and a shortened
    derivation proving your answer.
-/

section
namespace ex_67
-- Solution for (a)

variable {S : Type}
axiom Q : S → S → Prop

def M1 (x y : S) := ∀R : S → S → Prop, ((∀ z : S, R z z) → R x y)
def M2 (x y : S) := ∀R : S → S → Prop, ((∀u v : S, (Q u v → R u v)) → R x y)

theorem T : ∀a : S, M1 a a := by
  intro a
  have f := λR :  S → S → Prop => (λg : (∀ z : S, R z z) => g a)
  exact f


-- Solution for (b)

theorem T1 : ∀a b : S, (Q a b → M2 a b) := by
  intro a b
  intro q
  have f := λR : S → S → Prop => λg : (∀u v : S, (Q u v → R u v)) => g a b q
  exact f

end ex_67
end


/-
Exercise 6.8
  (a) Let Γ ≡ S : ∗, P : S → ∗. Find an inhabitant of the following
    type N in context Γ, and prove your answer by means of a shortened
    derivation:
    N ≡ [Πα : ∗. ((Πx : S. (Px → α)) → α)] → [Πx : S. (Px → ⊥)] → ⊥.
  (b) Which is the smallest system in the λ-cube in which your derivation
    may be executed?
  (c) The expression Πα : ∗. ((Πx : S. (Px → α)) → α may be considered
  as an encoding of ∃x ∈ S (P(x)). (We shall show this in Section 7.5.) In
  Section 7.1 we make plausible that A → ⊥ may be considered as an
  encoding of the negation ¬A. With these things in mind, how can we
  interpret the content of the expression N? (See also Figure 5.2.)
-/

section
namespace ex_68

-- Solution for (a)

axiom S : Type
axiom P : S → Prop

def N := (∀α : Prop, ((∀x : S, (P x → α)) → α)) → (∀x : S, (P x → Cont)) → Cont

theorem T : N := by
  intro p q
  exact p Cont q

-- Solution for (b) and (c)
-- Sorry

end ex_68
end


/-
Exercise 6.9
Given S : ∗, P : S → ∗ and f : S → S, we deﬁne in λC the expression:
M ≡ λx : S . ΠQ : S → ∗ . (Πz : S . (Q z → Q(f z))) → Q x.
Give a term of type Πa : S . (M a → M (f a)) and a (shortened) deriva-
tion proving this.
-/

-- Solution
section
namespace ex_69

variable {S : Type}
axiom P : S → Prop
axiom f : S → S

def M := λx : S => ∀ Q : S → Prop, (∀z : S, (Q z → Q (f z))) → Q x

example : ∀a : S, (M a → M (f a)) := by
  intro a p
  intro q x
  have h := x a
  have h1 := p q x
  exact h h1

end ex_69
end


/-
Exercise 6.10 Given S : ∗ and P1, P2 : S → ∗, we deﬁne in λC the expression:
  R ≡ λx : S. ΠQ : S → ∗ . (Πy : S . (P1 y → P2 y → Q y)) → Q x.
We claim that R codes ‘the intersection of P1 and P2 ’, i.e. the predicate
that holds if and only if both P1 and P2 hold. In order to show this, give
inhabitants of the following types, plus (shortened) derivations proving
this:
(a) Πx : S. (P1 x → P2 x → R x),
(b) Πx : S. (R x → P1 x),
(c) Πx : S. (R x → P2 x).
Why do (a), (b) and (c) entail that R is this intersection?
(Hint for (b): see Exercise 5.8 (a).)
-/

section
namespace ex_610

variable {S : Type}
axiom P1 : S → Prop
axiom P2 : S → Prop

def R := λx : S => ∀Q : S → Prop, (∀y : S, (P1 y → P2 y → Q y)) → Q x

-- Solution for (a)

example : ∀x : S, (P1 x → P2 x → R x) := by
  intro x p1 p2
  intro q h1
  have h2 := h1 x p1 p2
  exact h2

-- Solution for (b)

example : ∀x : S, (R x → P1 x) := by
  intro x r
  have q := r P1
  have f := λy : S => λg : P1 y => λ_ : P2 y => g
  exact q f

-- Solution for (c)

example : ∀x : S, (R x → P2 x) := by
  intro x r
  have q := r P2
  have f := λy : S => λ_ : P1 y => λg : P2 y => g
  exact q f

end ex_610

end
