import HoTTRijke.chapter3
import HoTTRijke.chapter4

namespace chapter5_myeq
universe u v w

/- This file contains our implementation of the equality type MyEq
   following the description in Chapter 5 in the HoTT book (Rijke).

-/

-- We define our own identity type (e.g., for Type Theory exercises):

inductive MyEq {α : Type} : α → α → Type where
  | refl (a : α) : MyEq a a

/-
   The induction principle for MyEq type is
   ind-eqₐ : P(a, reflₐ) →  Π(x:A). Π(p:a=x). P(x,p) giving
   ind_eqₐ(u,a,relfₐ) = u

   This says that if P(a,reflₐ) is true then for all x of the same type
   and for all proofs that a = x, we have that P(x,p) must also be true.

  More specifically, if u is a proof that P(a,reflₐ), x:A, and p is a proof
  that a = x, then ind_eqₐ(u,x,p) is a proof that P(x,p).

  Moreover, ind_eqₐ(u,a,relfₐ) = u; that is ind_eqₐ returns the same proof
  in this case.
-/

#check MyEq.rec

-- You can add notation
notation:100 a " ≡ " b => MyEq a b

def ind_eq {α : Type} {a : α}
    (P : (x : α) → (a ≡ x) → Type) : -- P is indexed by x : α and p : a ≡ x
    (P a (MyEq.refl a)) →  ((x : α) → (p : a ≡ x) → P x p) :=
  by
    intro h x p
    cases p
    exact h

-- Prove basic properties
def myEq_symm {α : Type} {a x : α} : (a ≡ x) → (x ≡ a) := by
  intro p -- p : a ≡ x
  /- At this point we want to prove x ≡ a. The type P(x,p) is 'x ≡ a'
     independent of p. -/
  let P : (x : α) → (a ≡ x) → Type := fun x _ => (x ≡ a)
  -- P a (MyEq.refl a) is 'a = a' and 'MyEq.refl a' is proof of this.
  -- thus we apply ind_eq
  exact ind_eq (α:=α) (a:=a) P (MyEq.refl a) x p


def myEq_symm_refl {α: Type} (a : α) : myEq_symm (MyEq.refl a) ≡ (MyEq.refl a) :=
  MyEq.refl _


 def myEq_refl {α : Type} {a : α} : (a ≡ a) := MyEq.refl a


 def myEq_trans {α : Type} {a x y : α} : (a ≡ x) → (x ≡ y) → (a ≡ y):= by
  intro p
  let P : (x' : α) → (a ≡ x') → Type := fun x' _ => (x' ≡ y) → (a ≡ y)
  exact ind_eq P (fun a => a) x p

instance {α : Type} : Trans (@MyEq α) (@MyEq α) (@MyEq α) where
  trans := myEq_trans

def concat_eq {α : Type} {x y z : α} : (x ≡ y) → (y ≡ z) → (x ≡ z) :=  by
  intro p
  let P : (y' : α) → (x ≡ y') → Type := fun y' _ => (y' ≡ z) → (x ≡ z)
  exact ind_eq P (fun a => a) y p


notation:60 a " • " b => concat_eq a b

def concat_assoc {α : Type} {a b c d : α} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) :
    (p • (q • r)) ≡ ((p • q) • r) := by
    cases p
    cases q
    cases r
    exact MyEq.refl _

def concat_right_unit {α : Type} {a b : α} (p : a ≡ b) : (p • (MyEq.refl b)) ≡ p := by
  cases p
  exact MyEq.refl (MyEq.refl a)

def concat_left_unit  {α : Type} {a b : α} (p : a ≡ b) : ((MyEq.refl a) • p) ≡ p := by
  cases p
  exact MyEq.refl (MyEq.refl a)


def ap {α : Type} {β : Type} (f : α → β) (x y : α) (p : x ≡ y) : (f x ≡ f y) := by
  let P : (y' : α) → (x ≡ y') → Type := fun y' _ => f x ≡ f y'
  exact ind_eq (α:=α) (a:=x) P (MyEq.refl (f x)) y p


def left_unit  {α : Type} {a b : α} (p : a ≡ b) : (a ≡ b) := (MyEq.refl a) • p
def right_unit {α : Type} {a b : α} (p : a ≡ b) : (a ≡ b) := p • MyEq.refl b

-- Exercise 5.1

def sym_contat_distributive {α : Type} {x y z : α} (p1 : x ≡ y ) (p2 : y ≡ z ) :
      myEq_symm (p1 • p2) ≡ (myEq_symm p2) • (myEq_symm p1) := by
        cases p1
        cases p2
        -- ⊢ myEq_symm (MyEq.refl x • MyEq.refl x) ≡ myEq_symm (MyEq.refl x) • myEq_symm (MyEq.refl x)
        exact
        (ap myEq_symm (MyEq.refl x • MyEq.refl x) (MyEq.refl x) (concat_right_unit (MyEq.refl x))) •
        myEq_symm_refl (x) •
        concat_right_unit (MyEq.refl x)

--Exercise 5.2

def inv_con {α : Type} {a b c : α} (p : a ≡ b) (q : b ≡ c) (r : a ≡ c) :
    ((p • q) ≡ r) → (q ≡ (myEq_symm p • r)) := by
    cases p
    cases q
    cases r
    --  ((MyEq.refl a • MyEq.refl a) ≡ MyEq.refl a) → MyEq.refl a ≡ myEq_symm (MyEq.refl a) • MyEq.refl a
    exact fun p => myEq_symm p

def con_inv {α : Type} {a b c : α} (p : a ≡ b) (q : b ≡ c) (r : a ≡ c) :
    ((p • q) ≡ r) → (p ≡ r • (myEq_symm q)) := by
    cases p
    cases q
    cases r
    --  ((MyEq.refl a • MyEq.refl a) ≡ MyEq.refl a) → MyEq.refl a ≡ myEq_symm (MyEq.refl a) • MyEq.refl a
    exact fun p => myEq_symm p


def ap_id {α : Type} (x y : α) (p : x ≡ y) : p ≡ (ap (fun (x:α) => x) x y p) := by
  let P : (y' : α) → (p' : x ≡ y') → Type := fun y' p' => p' ≡ (ap (fun (x:α) => x) x y' p')
  exact ind_eq (α:=α) (a:=x) P (MyEq.refl _) y p


def ap_comp {α : Type} {β : Type} {γ : Type} (f : α → β) (g : β → γ) (x y : α) (p : x ≡ y) : ap g (f x) (f y) (ap f x y  p) ≡ ap (g ∘ f) x y p := by
  let P (y' : α) (p' : x ≡ y') : Type :=
    ap g (f x) (f y') (ap f x y' p') ≡ ap (g ∘ f) x y' p'

  have u : P x (MyEq.refl x) :=
    MyEq.refl (MyEq.refl (g (f x)))

  exact ind_eq (α:=α) (a:=x) P u y p

def unique_ref {α : Type} (x y : α) (p : x ≡ y) :
  (⟨x, MyEq.refl x⟩ : Σ (y' : α ), x ≡ y') ≡ ⟨y, p⟩ :=
    by
      cases p
      exact MyEq.refl _

def transport {α : Type} {x y : α} (β : (x' : α) → Type) : (x ≡ y) → (β x → β y) :=
  by
    intro p q
    let β' : (y' : α) → (x ≡ y') → Type := fun y' _ => β y'
    exact ind_eq β' q y p


-- Exercise 5.3

def lift_β (α : Type) (β : (a : α) → Type) (a x : α) (b : β a) (p : a ≡ x) :
  (⟨a, b⟩ : Σ a, β a) ≡ ⟨x, transport β p b⟩ := by
  cases p
  have q : transport β (MyEq.refl a) b  ≡ b :=
    MyEq.refl b
  exact  ap (fun c => (⟨a, c⟩ : Σ a, β a)) (transport β (MyEq.refl a) b) b q

-- Exercise 5.4

def maclane_pentagon {α : Type} (a b c d e : α) (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) : Type := by
  have α₁ : (((p • q) • r) • s) ≡ ((p • (q • r)) • s) := by
    have h := myEq_symm (concat_assoc p q r)
    let rs (p' : a ≡ d) : a ≡ e := concat_eq p' s
    have h' := ap rs ((p • q) • r) (p • (q • r)) h
    exact h'

  have α₂ : ((p • (q • r)) • s) ≡ (p • (q • r) • s) := by
    have h := myEq_symm (concat_assoc p (q • r) s)
    exact h

  have α₃ : (p • ((q • r) • s)) ≡ (p • (q • (r • s))) := by
    have h := myEq_symm (concat_assoc q r s)
    let rs (p' : b ≡ e) : a ≡ e := concat_eq p p'
    have h' := ap rs ((q • r) • s) (q • (r • s)) h
    exact h'

  have α₄ : (((p • q) • r) • s) ≡ ((p • q) • (r • s)) := by
    have h := myEq_symm (concat_assoc (p • q) r s)
    exact h

  have α₅ : ((p • q) • (r • s)) ≡ (p • (q • (r • s))) := by
    have h := myEq_symm (concat_assoc p q (r • s))
    exact h

  have t : ((α₁ • α₂) • α₃) ≡ (α₄ • α₅) := by
    induction s
    induction r
    induction q
    induction p
    cases ((α₁ • α₂) • α₃)
    cases α₄ • α₅
    exact MyEq.refl (MyEq.refl (((MyEq.refl a • MyEq.refl a) • MyEq.refl a) • MyEq.refl a))

  exact α

end chapter5_myeq
