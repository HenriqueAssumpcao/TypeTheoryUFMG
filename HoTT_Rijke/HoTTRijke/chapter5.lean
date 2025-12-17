import HoTT_Rijke.chapter3

open chapter3


universe u v w

-- If you want to define your own identity type (e.g., for Type Theory exercises):

inductive MyEq {α : Type u} : α → α → Type u where
  | refl (a : α) : MyEq a a

-- The induction principle for MyEq type is
-- ind-eqₐ : P(a, reflₐ) →  Π(x:A). Π(p:a=x). P(x,p) giving
-- ind_eqₐ(u,a,relfₐ) = u

-- You can add notation
notation:50 a " ≡ " b => MyEq a b


def ind_eq {α : Type u} {a : α}
    (P : (x : α) → (a ≡ x) → Type u) : -- P is indexed by x : α and p : a ≡ x
    (P a (MyEq.refl a)) →  ((x : α) → (p : a ≡ x) → P x p) :=
  by
    intro h x p
    cases p
    simpa using h


-- Prove basic properties
def myEq_symm {α : Type u} {a x : α} : (a ≡ x) → (x ≡ a) := by
  intro p -- p : a ≡ x
  /- At this point we want to prove x ≡ a. The type P(x,p) is 'x ≡ a'
     independent of p. -/
  let P : (x : α) → (a ≡ x) → Type u := fun x _ => (x ≡ a)

  -- P a (MyEq.refl a) is 'a = a' and 'MyEq.refl a' is proof of this.
  -- thus we apply ind_eq
  exact ind_eq (α:=α) (a:=a) P (MyEq.refl a) x p


 def myEq_refl {α : Type u} {a : α} : (a ≡ a) := MyEq.refl a

 def myEq_trans {α : Type u} {a x y : α} : (a ≡ x) → (x ≡ y) → (a ≡ y):= by
  intro p
  let P : (x' : α) → (a ≡ x') → Type u := fun x' _ => (x' ≡ y) → (a ≡ y)
  exact ind_eq P (fun a => a) x p

def concat_eq {α : Type u} {x y z : α} : (x ≡ y) → (y ≡ z) → (x ≡ z) :=  by
  intro p
  let P : (y' : α) → (x ≡ y') → Type u := fun y' _ => (y' ≡ z) → (x ≡ z)
  exact ind_eq P (fun a => a) y p

notation:50 a " • " b => concat_eq a b

def concat_assoc {α : Type u} {a b c d : α} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) :
    (p • (q • r)) ≡ ((p • q) • r) := by
    cases p
    cases q
    cases r
    exact MyEq.refl _


def left_unit  {α : Type u} {a b : α} (p : a ≡ b) : (a ≡ b) := (MyEq.refl a) • p
def right_unit {α : Type u} {a b : α} (p : a ≡ b) : (a ≡ b) := p • MyEq.refl b


def ap {α : Type u} {β : Type u} (f : α → β) (x y : α) (p : x ≡ y) : (f x ≡ f y) := by
  let P : (y' : α) → (x ≡ y') → Type u := fun y' _ => f x ≡ f y'
  exact ind_eq (α:=α) (a:=x) P (MyEq.refl (f x)) y p

def ap_id {α : Type u} (x y : α) (p : x ≡ y) : p ≡ (ap (fun (x:α) => x) x y p) := by
  let P : (y' : α) → (p' : x ≡ y') → Type u := fun y' p' => p' ≡ (ap (fun (x:α) => x) x y' p')
  exact ind_eq (α:=α) (a:=x) P (MyEq.refl _) y p



def ap_comp {α : Type u} {β : Type u} {γ : Type u} (f : α → β) (g : β → γ) (x y : α) (p : x ≡ y) :
  ap g (f x) (f y) (ap f x y  p) ≡ ap (g ∘ f) x y p := by
  let t := ap  f x x (MyEq.refl x)
  let s := ap_id x x (MyEq.refl x)
  let P : (y' : α) → (p' : x ≡ y') → Type u :=
    fun y' p' => ap g (f x) (f y') (ap f x y' p') ≡ ap (g ∘ f) x y' p'
  have u : P x (MyEq.refl x) := sorry
  exact ind_eq (α:=α) (a:=x) P u y p


def unique_ref {α : Type u} (x y : α) (p : x ≡ y) :
  (⟨x, MyEq.refl x⟩ : Σ (y' : α ), x ≡ y') ≡ ⟨y, p⟩ :=
    by
      cases p
      exact MyEq.refl _


def transport {α : Type u} (x y : α) (β : (x' : α) → Type (u+1)) : (x ≡ y) → (β x ≡ β y) := 
  by 
    sorry 
    /- let P : (y' : α) → (p' : x ≡ y') → Type (u + 1) := fun y' p => (x ≡ y') → (β x ≡ β y')
       exact ind_eq (α:=α) (a:=x) P y p -/
