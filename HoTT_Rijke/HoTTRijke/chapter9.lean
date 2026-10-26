/-
  Chapter 9 — Equivalences

  Sections 9.1–9.3 of Rijke's Introduction to Homotopy Type Theory.
  As in Chapter 5, identities inhabit Type, and proofs are definitions.
  MyEq and myProd in this project are restricted to Type 0; this chapter
  deliberately retains that restriction and those existing definitions.
  No function extensionality is needed. Exercises are not included.
-/

import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_ints
import HoTTRijke.chapter7

open chapter5_myeq chapter3_booleans

namespace chapter9

/- ###################################################################### -/
/-  9.1 Homotopies                                                       -/
/- ###################################################################### -/

-- Definition 9.1.2 (also for dependent functions).
def htpy {A : Type} {B : A → Type} (f g : (x : A) → B x) : Type :=
  (x : A) → f x ≡ g x

-- Remark 9.1.1 and Example 9.1.3.
def neg_bool_involutive : htpy (myNeg ∘ myNeg) id
  | myBool.myTrue => MyEq.refl _
  | myBool.myFalse => MyEq.refl _

-- Definition 9.1.5.
def refl_htpy {A : Type} {B : A → Type} (f : (x : A) → B x) : htpy f f :=
  fun x => MyEq.refl (f x)

def inv_htpy {A : Type} {B : A → Type} {f g : (x : A) → B x}
    (H : htpy f g) : htpy g f := fun x => myEq_symm (H x)

def concat_htpy {A : Type} {B : A → Type} {f g h : (x : A) → B x}
    (H : htpy f g) (K : htpy g h) : htpy f h := fun x => H x • K x

-- Proposition 9.1.6: laws are homotopies, not equalities of functions.
def assoc_htpy {A : Type} {B : A → Type} {f g h i : (x : A) → B x}
    (H : htpy f g) (K : htpy g h) (L : htpy h i) :
    htpy (concat_htpy (concat_htpy H K) L) (concat_htpy H (concat_htpy K L)) :=
  fun x => myEq_symm (concat_assoc (H x) (K x) (L x))

def left_unit_htpy {A : Type} {B : A → Type} {f g : (x : A) → B x}
    (H : htpy f g) : htpy (concat_htpy (refl_htpy f) H) H :=
  fun x => concat_left_unit (H x)

def right_unit_htpy {A : Type} {B : A → Type} {f g : (x : A) → B x}
    (H : htpy f g) : htpy (concat_htpy H (refl_htpy g)) H :=
  fun x => concat_right_unit (H x)

def left_inv_htpy {A : Type} {B : A → Type} {f g : (x : A) → B x}
    (H : htpy f g) : htpy (concat_htpy (inv_htpy H) H) (refl_htpy g) := by
  intro x
  have cancel {X : Type} {a b : X} (p : a ≡ b) :
      (myEq_symm p • p) ≡ MyEq.refl b := by
    cases p
    exact MyEq.refl _
  exact cancel (H x)

def right_inv_htpy {A : Type} {B : A → Type} {f g : (x : A) → B x}
    (H : htpy f g) : htpy (concat_htpy H (inv_htpy H)) (refl_htpy f) := by
  intro x
  have cancel {X : Type} {a b : X} (p : a ≡ b) :
      (p • myEq_symm p) ≡ MyEq.refl a := by
    cases p
    exact MyEq.refl _
  exact cancel (H x)

-- Definition 9.1.7.
def left_whisker {A B C : Type} {f g : A → B} (h : B → C)
    (H : htpy f g) : htpy (h ∘ f) (h ∘ g) := fun x => ap h _ _ (H x)

def right_whisker {A B C : Type} {g h : B → C} (H : htpy g h)
    (f : A → B) : htpy (g ∘ f) (h ∘ f) := fun x => H (f x)

/- ###################################################################### -/
/-  9.2 Bi-invertible maps                                               -/
/- ###################################################################### -/

-- Definition 9.2.1. myEquiv from Chapter 3 is only logical equivalence;
-- equivalences here additionally carry the two inverse homotopies.
def sec {A B : Type} (f : A → B) : Type := Σ g : B → A, htpy (f ∘ g) id

def retr {A B : Type} (f : A → B) : Type := Σ h : B → A, htpy (h ∘ f) id

def is_equiv {A B : Type} (f : A → B) : Type := myProd (sec f) (retr f)

def equiv (A B : Type) : Type := Σ f : A → B, is_equiv f

def inv_equiv {A B : Type} (e : equiv A B) : B → A := (proj1 e.2).1

-- Example 9.2.3.
def equiv_id (A : Type) : equiv A A :=
  ⟨id, myProd.mk ⟨id, refl_htpy id⟩ ⟨id, refl_htpy id⟩⟩

-- Example 9.2.4.
def equiv_neg_bool : equiv myBool myBool :=
  ⟨myNeg, myProd.mk ⟨myNeg, neg_bool_involutive⟩ ⟨myNeg, neg_bool_involutive⟩⟩

-- Example 9.2.5: the integer operations of Chapters 3–5.
open chapter3_integers chapter4_integers Integers

def equiv_succZ : equiv myZ myZ :=
  ⟨succZ, myProd.mk ⟨predZ, succ_pred_elim⟩ ⟨predZ, pred_succ_elim⟩⟩

def equiv_predZ : equiv myZ myZ :=
  ⟨predZ, myProd.mk ⟨succZ, pred_succ_elim⟩ ⟨succZ, succ_pred_elim⟩⟩

def equiv_addZ (k : myZ) : equiv myZ myZ :=
  ⟨fun x => myAddZ x k, myProd.mk
    ⟨fun x => myAddZ x (negative k), fun x =>
      myEq_symm (add_associative_Z x (negative k) k) •
      ap (myAddZ x) _ _ (add_left_inverse k) • right_add_zero x⟩
    ⟨fun x => myAddZ x (negative k), fun x =>
      myEq_symm (add_associative_Z x k (negative k)) •
      ap (myAddZ x) _ _ (add_right_inverse k) • right_add_zero x⟩⟩

def negative_involutive : htpy (negative ∘ negative) id
  | Sum.inl _ => MyEq.refl _
  | Sum.inr (Sum.inl ()) => MyEq.refl _
  | Sum.inr (Sum.inr _) => MyEq.refl _

def equiv_negative : equiv myZ myZ :=
  ⟨negative, myProd.mk ⟨negative, negative_involutive⟩ ⟨negative, negative_involutive⟩⟩

-- Example 9.2.5, continued: cyclic operations on the existing finite types.
def equiv_succ_fin (k : chapter3_naturals_with_zero.myN) : equiv (myFin k) (myFin k) :=
  ⟨succ_fin k, myProd.mk ⟨pred_fin k, succ_pred_fin k⟩ ⟨pred_fin k, pred_succ_fin k⟩⟩

def equiv_pred_fin (k : chapter3_naturals_with_zero.myN) : equiv (myFin k) (myFin k) :=
  ⟨pred_fin k, myProd.mk ⟨succ_fin k, pred_succ_fin k⟩ ⟨succ_fin k, succ_pred_fin k⟩⟩

def equiv_add_fin (k : chapter3_naturals_with_zero.myN) (a : myFin k) :
    equiv (myFin k) (myFin k) :=
  ⟨fun x => add_fin k x a, myProd.mk
    ⟨fun x => add_fin k x (neg_fin k a), fun x => add_fin_cancel_neg_left k x a⟩
    ⟨fun x => add_fin k x (neg_fin k a), fun x => add_fin_cancel_neg k x a⟩⟩

def equiv_neg_fin (k : chapter3_naturals_with_zero.myN) : equiv (myFin k) (myFin k) :=
  ⟨neg_fin k, myProd.mk ⟨neg_fin k, neg_fin_involutive k⟩ ⟨neg_fin k, neg_fin_involutive k⟩⟩

-- Remark 9.2.6.
def has_inverse {A B : Type} (f : A → B) : Type :=
  Σ g : B → A, myProd (htpy (f ∘ g) id) (htpy (g ∘ f) id)

def is_equiv_of_has_inverse {A B : Type} {f : A → B}
    (I : has_inverse f) : is_equiv f :=
  myProd.mk ⟨I.1, proj1 I.2⟩ ⟨I.1, proj2 I.2⟩

-- Constructor used below to exhibit the maps and both homotopies explicitly.
def equiv_of_inverse {A B : Type} (f : A → B) (g : B → A)
    (G : htpy (f ∘ g) id) (H : htpy (g ∘ f) id) : equiv A B :=
  ⟨f, is_equiv_of_has_inverse ⟨g, myProd.mk G H⟩⟩

-- Proposition 9.2.7: compare the independently supplied section and retraction.
def htpy_sec_retr {A B : Type} {f : A → B} (s : sec f) (r : retr f) :
    htpy s.1 r.1 :=
  concat_htpy (inv_htpy (right_whisker r.2 s.1)) (left_whisker r.1 s.2)

def has_inverse_of_is_equiv {A B : Type} {f : A → B}
    (E : is_equiv f) : has_inverse f :=
  let s := proj1 E
  let r := proj2 E
  ⟨s.1, myProd.mk s.2 (concat_htpy (right_whisker (htpy_sec_retr s r) f) r.2)⟩

-- Corollary 9.2.8. The inverse map is exactly the chosen section.
def is_equiv_inv {A B : Type} (e : equiv A B) : is_equiv (inv_equiv e) :=
  let I := has_inverse_of_is_equiv e.2
  is_equiv_of_has_inverse ⟨e.1, myProd.mk (proj2 I.2) (proj1 I.2)⟩

def equiv_inv {A B : Type} (e : equiv A B) : equiv B A :=
  ⟨inv_equiv e, is_equiv_inv e⟩

-- Example 9.2.9: coproduct and product laws.
-- Sum is the coproduct used throughout Chapters 3 and 7–8; products use myProd.
def equiv_empty_sum (B : Type) : equiv (Empty ⊕ B) B :=
  equiv_of_inverse (fun s => match s with
    | Sum.inl e => nomatch e
    | Sum.inr b => b) Sum.inr
    (fun _ => MyEq.refl _) (fun s => match s with
      | Sum.inl e => nomatch e
      | Sum.inr _ => MyEq.refl _)

def equiv_sum_empty (A : Type) : equiv (A ⊕ Empty) A :=
  equiv_of_inverse (fun s => match s with
    | Sum.inl a => a
    | Sum.inr e => nomatch e) Sum.inl
    (fun _ => MyEq.refl _) (fun s => match s with
      | Sum.inl _ => MyEq.refl _
      | Sum.inr e => nomatch e)

def equiv_sum_comm (A B : Type) : equiv (A ⊕ B) (B ⊕ A) :=
  equiv_of_inverse
    (fun s => match s with | Sum.inl a => Sum.inr a | Sum.inr b => Sum.inl b)
    (fun s => match s with | Sum.inl b => Sum.inr b | Sum.inr a => Sum.inl a)
    (fun s => match s with | Sum.inl _ => MyEq.refl _ | Sum.inr _ => MyEq.refl _)
    (fun s => match s with | Sum.inl _ => MyEq.refl _ | Sum.inr _ => MyEq.refl _)

def equiv_sum_assoc (A B C : Type) : equiv ((A ⊕ B) ⊕ C) (A ⊕ (B ⊕ C)) :=
  equiv_of_inverse
    (fun s => match s with
      | Sum.inl (Sum.inl a) => Sum.inl a
      | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
      | Sum.inr c => Sum.inr (Sum.inr c))
    (fun s => match s with
      | Sum.inl a => Sum.inl (Sum.inl a)
      | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
      | Sum.inr (Sum.inr c) => Sum.inr c)
    (fun s => match s with
      | Sum.inl _ => MyEq.refl _
      | Sum.inr (Sum.inl _) => MyEq.refl _
      | Sum.inr (Sum.inr _) => MyEq.refl _)
    (fun s => match s with
      | Sum.inl (Sum.inl _) => MyEq.refl _
      | Sum.inl (Sum.inr _) => MyEq.refl _
      | Sum.inr _ => MyEq.refl _)

def equiv_empty_prod (B : Type) : equiv (myProd Empty B) Empty :=
  equiv_of_inverse proj1 Empty.elim (fun e => nomatch e)
    (fun p => nomatch proj1 p)

def equiv_prod_empty (A : Type) : equiv (myProd A Empty) Empty :=
  equiv_of_inverse proj2 Empty.elim (fun e => nomatch e)
    (fun p => nomatch proj2 p)

def equiv_unit_prod (B : Type) : equiv (myProd Unit B) B :=
  equiv_of_inverse proj2 (myProd.mk ()) (fun _ => MyEq.refl _)
    (fun p => match p with | myProd.mk () _ => MyEq.refl _)

def equiv_prod_unit (A : Type) : equiv (myProd A Unit) A :=
  equiv_of_inverse proj1 (fun a => myProd.mk a ()) (fun _ => MyEq.refl _)
    (fun p => match p with | myProd.mk _ () => MyEq.refl _)

def equiv_prod_comm (A B : Type) : equiv (myProd A B) (myProd B A) :=
  equiv_of_inverse (fun p => myProd.mk (proj2 p) (proj1 p))
    (fun p => myProd.mk (proj2 p) (proj1 p))
    (fun p => match p with | myProd.mk _ _ => MyEq.refl _)
    (fun p => match p with | myProd.mk _ _ => MyEq.refl _)

def equiv_prod_assoc (A B C : Type) :
    equiv (myProd (myProd A B) C) (myProd A (myProd B C)) :=
  equiv_of_inverse
    (fun p => match p with | myProd.mk (myProd.mk a b) c => myProd.mk a (myProd.mk b c))
    (fun p => match p with | myProd.mk a (myProd.mk b c) => myProd.mk (myProd.mk a b) c)
    (fun p => match p with | myProd.mk _ (myProd.mk _ _) => MyEq.refl _)
    (fun p => match p with | myProd.mk (myProd.mk _ _) _ => MyEq.refl _)

def equiv_prod_sum (A B C : Type) :
    equiv (myProd A (B ⊕ C)) ((myProd A B) ⊕ (myProd A C)) :=
  equiv_of_inverse
    (fun p => match p with
      | myProd.mk a (Sum.inl b) => Sum.inl (myProd.mk a b)
      | myProd.mk a (Sum.inr c) => Sum.inr (myProd.mk a c))
    (fun s => match s with
      | Sum.inl (myProd.mk a b) => myProd.mk a (Sum.inl b)
      | Sum.inr (myProd.mk a c) => myProd.mk a (Sum.inr c))
    (fun s => match s with
      | Sum.inl (myProd.mk _ _) => MyEq.refl _
      | Sum.inr (myProd.mk _ _) => MyEq.refl _)
    (fun p => match p with
      | myProd.mk _ (Sum.inl _) => MyEq.refl _
      | myProd.mk _ (Sum.inr _) => MyEq.refl _)

def equiv_sum_prod (A B C : Type) :
    equiv (myProd (A ⊕ B) C) ((myProd A C) ⊕ (myProd B C)) :=
  equiv_of_inverse
    (fun p => match p with
      | myProd.mk (Sum.inl a) c => Sum.inl (myProd.mk a c)
      | myProd.mk (Sum.inr b) c => Sum.inr (myProd.mk b c))
    (fun s => match s with
      | Sum.inl (myProd.mk a c) => myProd.mk (Sum.inl a) c
      | Sum.inr (myProd.mk b c) => myProd.mk (Sum.inr b) c)
    (fun s => match s with
      | Sum.inl (myProd.mk _ _) => MyEq.refl _
      | Sum.inr (myProd.mk _ _) => MyEq.refl _)
    (fun p => match p with
      | myProd.mk (Sum.inl _) _ => MyEq.refl _
      | myProd.mk (Sum.inr _) _ => MyEq.refl _)

-- Example 9.2.10: the corresponding dependent pair laws.
def equiv_sigma_empty_base (B : Empty → Type) : equiv (Σ x, B x) Empty :=
  equiv_of_inverse Sigma.fst Empty.elim (fun e => nomatch e)
    (fun s => nomatch s.1)

def equiv_sigma_empty_fiber (A : Type) : equiv (Σ _ : A, Empty) Empty :=
  equiv_of_inverse Sigma.snd Empty.elim (fun e => nomatch e)
    (fun s => nomatch s.2)

def equiv_sigma_unit_base (B : Unit → Type) : equiv (Σ x, B x) (B ()) :=
  equiv_of_inverse (fun s => match s with | ⟨(), b⟩ => b)
    (fun b => ⟨(), b⟩) (fun _ => MyEq.refl _)
    (fun s => match s with | ⟨(), _⟩ => MyEq.refl _)

def equiv_sigma_unit_fiber (A : Type) : equiv (Σ _ : A, Unit) A :=
  equiv_of_inverse Sigma.fst (fun a => ⟨a, ()⟩) (fun _ => MyEq.refl _)
    (fun s => match s with | ⟨_, ()⟩ => MyEq.refl _)

def equiv_sigma_assoc {A : Type} {B : A → Type} (C : (Σ x, B x) → Type) :
    equiv (Σ w, C w) (Σ x, Σ y, C ⟨x, y⟩) :=
  equiv_of_inverse (fun s => ⟨s.1.1, s.1.2, s.2⟩)
    (fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩)
    (fun _ => MyEq.refl _) (fun _ => MyEq.refl _)

def equiv_sigma_assoc_family {A : Type} {B : A → Type}
    (C : (x : A) → B x → Type) :
    equiv (Σ w : (Σ x, B x), C w.1 w.2) (Σ x, Σ y, C x y) :=
  equiv_sigma_assoc (fun w => C w.1 w.2)

def equiv_sigma_sum {A : Type} (B C : A → Type) :
    equiv (Σ x, B x ⊕ C x) ((Σ x, B x) ⊕ (Σ x, C x)) :=
  equiv_of_inverse
    (fun s => match s with
      | ⟨x, Sum.inl b⟩ => Sum.inl ⟨x, b⟩
      | ⟨x, Sum.inr c⟩ => Sum.inr ⟨x, c⟩)
    (fun s => match s with
      | Sum.inl ⟨x, b⟩ => ⟨x, Sum.inl b⟩
      | Sum.inr ⟨x, c⟩ => ⟨x, Sum.inr c⟩)
    (fun s => match s with | Sum.inl ⟨_, _⟩ => MyEq.refl _ | Sum.inr ⟨_, _⟩ => MyEq.refl _)
    (fun s => match s with | ⟨_, Sum.inl _⟩ => MyEq.refl _ | ⟨_, Sum.inr _⟩ => MyEq.refl _)

def equiv_sigma_sum_base {A B : Type} (C : A ⊕ B → Type) :
    equiv (Σ w, C w) ((Σ x, C (Sum.inl x)) ⊕ (Σ y, C (Sum.inr y))) :=
  equiv_of_inverse
    (fun s => match s with
      | ⟨Sum.inl a, c⟩ => Sum.inl ⟨a, c⟩
      | ⟨Sum.inr b, c⟩ => Sum.inr ⟨b, c⟩)
    (fun s => match s with
      | Sum.inl ⟨a, c⟩ => ⟨Sum.inl a, c⟩
      | Sum.inr ⟨b, c⟩ => ⟨Sum.inr b, c⟩)
    (fun s => match s with | Sum.inl ⟨_, _⟩ => MyEq.refl _ | Sum.inr ⟨_, _⟩ => MyEq.refl _)
    (fun s => match s with | ⟨Sum.inl _, _⟩ => MyEq.refl _ | ⟨Sum.inr _, _⟩ => MyEq.refl _)

-- Remark 9.2.11: no equivalences of function types are asserted here.

/- ###################################################################### -/
/-  9.3 Characterizing the identity types of Σ-types                      -/
/- ###################################################################### -/

-- Definition 9.3.1.
def Eq_sigma {A : Type} {B : A → Type} (s t : Σ x, B x) : Type :=
  Σ p : s.1 ≡ t.1, transport B p s.2 ≡ t.2

-- Lemma 9.3.2.
def reflexive_Eq_sigma {A : Type} {B : A → Type} (s : Σ x, B x) : Eq_sigma s s :=
  ⟨MyEq.refl s.1, MyEq.refl s.2⟩

-- Definition 9.3.3.
def pair_eq {A : Type} {B : A → Type} {s t : Σ x, B x}
    (p : s ≡ t) : Eq_sigma s t := by
  cases p
  exact reflexive_Eq_sigma s

-- Theorem 9.3.4: inverse map, section, retraction, and equivalence.
def eq_pair {A : Type} {B : A → Type} {s t : Σ x, B x}
    (p : Eq_sigma s t) : s ≡ t := by
  rcases s with ⟨x, y⟩
  rcases t with ⟨x', y'⟩
  rcases p with ⟨p, q⟩
  cases p
  cases q
  exact MyEq.refl _

def pair_eq_eq_pair {A : Type} {B : A → Type} {s t : Σ x, B x}
    (p : Eq_sigma s t) : pair_eq (eq_pair p) ≡ p := by
  rcases s with ⟨x, y⟩
  rcases t with ⟨x', y'⟩
  rcases p with ⟨p, q⟩
  cases p
  cases q
  exact MyEq.refl _

def eq_pair_pair_eq {A : Type} {B : A → Type} {s t : Σ x, B x}
    (p : s ≡ t) : eq_pair (pair_eq p) ≡ p := by
  cases p
  exact MyEq.refl _

def is_equiv_pair_eq {A : Type} {B : A → Type} (s t : Σ x, B x) :
    is_equiv (pair_eq (s := s) (t := t)) :=
  is_equiv_of_has_inverse ⟨eq_pair, myProd.mk pair_eq_eq_pair eq_pair_pair_eq⟩

def equiv_eq_sigma {A : Type} {B : A → Type} (s t : Σ x, B x) :
    equiv (s ≡ t) (Eq_sigma s t) := ⟨pair_eq, is_equiv_pair_eq s t⟩

end chapter9
