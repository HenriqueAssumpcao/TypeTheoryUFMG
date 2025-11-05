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


/-
Exercise 5.8
  (a) Let Γ ≡ S: ∗, P: S → ∗, Q: S → ∗. Find an inhabitant of
Πx : S. Px → Qx → Px with respect to Γ, and give a corresponding
(shortened) derivation.
  (b) Give a natural deduction proof of the corresponding logical expression.
-/

-- Solution for (a)
section
namespace ex_58a

variable (S : Type) (P : S → Type) (Q : S → Type)

example : ∀x : S, P x → Q x → P x :=
  λ x : S => λy : P x => λ_ : Q x => y

end ex_58a
end

-- Solution for (b)
section
namespace ex_58b

variable (S : Type) (P Q : S → Prop)

theorem T : ∀x : S, P x → Q x → P x := by
  intro h
  intro h1
  intro h2
  exact h1

-- This is not excatly what the problem asked, but it's fine.

end ex_58b
end


/-
Exercise 5.9
Give proofs that the following propositions are tautologies, (first) in natural
deduction and (second) by means of a shortened λP-derivation.
  (a) ∀x ∈ S (Q(x)) ⇒ ∀y ∈ S (P(y) ⇒ Q(y)),
  (b) ∀x ∈ S (P(x) ⇒ Q(x)) ⇒ (∀y ∈ S (P(y)) ⇒ ∀z ∈ S (Q(z))).
-/

section
namespace ex_59
variable (S : Type) (Q P : S → Prop)

-- Solution for (a)

theorem A : (∀x : S, Q x) → (∀y : S, (P y → Q y)) := by
  intro h
  intro h1
  intro h2
  exact h h1

-- Solution for (b)

theorem B : (∀x : S, (P x → Q x)) → ((∀y : S, P y) → (∀z : S, Q z)) := by
  intro h
  intro h1
  intro h2
  have Py := h1 h2
  have P_Q := h h2
  exact P_Q Py

end ex_59
end


/-
Exercise 5.10
Consider the following context:
Γ ≡ S : ∗, P : S → ∗, f : S → S, g : S → S,
  u : Πx : S. (P(fx) → P(gx)), v: Πx,y : S. ((Px → Py) → P(fx))
Let M ≡ λx : S. v(fx)(gx)(ux).
  (a) Make a guess at which type N may satisfy Γ ⊢ M : N
  (b) Demonstrate that the proof object M does indeed code a proof of the
proposition N you have guessed, by elaborating the λP-derivation
corresponding to M.
-/

-- Solution for (a)
-- Πx : S. P(f(fx))

-- Solution for (b)
section
namespace ex_510b

variable {S : Type}
axiom P : S → Prop
axiom f : S → S
axiom g : S → S
axiom v : ∀x y : S, ((P x → P y) → P (f x))
axiom u : ∀x : S, (P (f x) → P (g x))

def M (x : S) := v (f x) (g x) (u x)

example: ∀x : S, P (f (f x)) := M

end ex_510b
end


/-
Exercise 5.11
Let S be a set, with Q and R relations on S × S, and let f and g be
functions from S to S. Assume that ∀x,y ∈ S (Q(x,f(y)) ⇒ Q(g(x),y)),
∀x,y ∈ S (Q(x,f(y)) ⇒ R(x,y)), and ∀x ∈ S(Q(x,f(f(x)))).
Prove that ∀x ∈ S (R(g(g(x)),g(x))) by giving a context Γ and finding a
term M such that:
Γ ⊢ M : Πx:S. R(g(gx))(gx).
Give the corresponding (shortened) λP-derivation.
-/

-- Solution
section
namespace ex_511

variable {S: Type} {Q R : S → S → Prop} {f g : S → S}

variable( t : ∀ x y: S, Q x (f y) → Q (g x) y )
axiom t' : ∀ x y: S, Q x (f y) → Q (g x) y

variable( s : ∀ x y: S, Q x (f y) → R x y )
axiom s' : ∀ x y: S, Q x (f y) → R x y

variable( u : ∀ x: S, Q x (f (f x)))
axiom u' : ∀ x: S, Q x (f (f x))

#check u'

example : ∀ x: S, R (g (g x)) (g x) := by
  intro x
  have q : Q (g x) (f (f (g x))) := u' (g x)
  have q1 : Q (g (g x)) (f (g x)) := t (g x) (f (g x)) q
  exact  s (g (g x)) (g x) q1

example : ∀ x: S, R (g (g x)) (g x) := by
  intro x
  have q : Q (g x) (f (f (g x))) := u' (g x)
  have q1 : Q (g (g x)) (f (g x)) := t' (g x) (f (g x)) q
  exact  s' (g (g x)) (g x) q1

end ex_511
end


/-
Exercise 5.12
In λP, consider the context
Γ ≡ S: ∗, R: S → S → ∗, u: Πx,y: S. Rxy → Ryx,
v : Πx,y,z : S. Rxy → Rxz → Ryz.
  (a) Show that R is ‘reflexive on its domain’, by constructing an inhabitant
    of the type Πx,y : S. Rxy → Rxx in context Γ; give a corresponding
    (shortened) derivation.
  (b) Show that R is transitive by constructing an inhabitant of the type
    Πx,y,z : S. Rxy → Ryz → Rxz in context Γ; give acorresponding
    (shortened) derivation.
-/

section
variable {S : Type} {R : S → S → Prop} {u : ∀x y : S, R x y → R y x} {v : ∀x y z : S,  R x y → R x z → R y z}

-- Solution for (a)

example : ∀x y : S, R x y → R x x := by
  intro x y
  intro p
  have q := u x y p
  have q1 := v y x x q q
  exact q1

-- Solution for (b)

example : ∀x y z : S, R x y → R y z → R x z := by
  intro x y z
  intro p p1
  have q := u x y p
  have q1 := v y x z q p1
  exact q1

end
