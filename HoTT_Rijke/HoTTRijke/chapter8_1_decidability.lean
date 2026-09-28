/-
  Chapter 8.1 — Decidability and decidable equality

  A type A is decidable if it comes equipped with an element of A + ¬A.
  We show that decidability is closed under +, × and → (Table 8.1), that the
  observational equality, ≤ and < on ℕ are decidable (Example 8.1.4), that ℕ and
  the standard finite types have decidable equality (Propositions 8.1.7 and 8.1.8),
  and that divisibility is decidable (Theorem 8.1.9).

  Conventions (see chapter8_0_preliminaries.lean):
  * ℕ is the 0-based `myN` of chapter3_naturals_with_zero.lean;
  * identifications are elements of `MyEq` (notation `≡`) of chapter5_eq.lean;
  * ¬A is `myNegType A := A → Empty`, A × B is `myProd A B` and A ↔ B is
    `myEquiv A B := myProd (A → B) (B → A)`, all from chapter3.lean;
  * A + B is Lean's `Sum A B` (as in chapter7.lean).
-/

import HoTTRijke.chapter7
import HoTTRijke.chapter8_0_preliminaries

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans
open chapter6_Universes
open props_naturals_with_zero

namespace chapter8

/- ###################################################################### -/
/-  Definition 8.1.1                                                       -/
/- ###################################################################### -/

-- is-decidable(A) := A + ¬A
abbrev is_decidable (A : Type) : Type := A ⊕ myNegType A

-- A family P over X is decidable if every P(x) is decidable.
abbrev is_decidable_family {X : Type} (P : X → Type) : Type := (x : X) → is_decidable (P x)


/- ###################################################################### -/
/-  Example 8.1.2                                                          -/
/- ###################################################################### -/

def is_decidable_unit : is_decidable Unit := Sum.inl ()

def is_decidable_empty : is_decidable Empty := Sum.inr id

-- Any type equipped with an element is decidable.
def is_decidable_of_elem {A : Type} (a : A) : is_decidable A := Sum.inl a



/- ###################################################################### -/
/-  Example 8.1.3 (Table 8.1): decidability of +, × and →                  -/
/- ###################################################################### -/

def is_decidable_sum {A B : Type} : is_decidable A → is_decidable B → is_decidable (A ⊕ B)
  | Sum.inl a, Sum.inl _ => Sum.inl (Sum.inl a)
  | Sum.inl a, Sum.inr _ => Sum.inl (Sum.inl a)
  | Sum.inr _, Sum.inl b => Sum.inl (Sum.inr b)
  | Sum.inr f, Sum.inr g =>
      Sum.inr (fun x => match x with
                        | Sum.inl a => f a
                        | Sum.inr b => g b)

def is_decidable_prod {A B : Type} : is_decidable A → is_decidable B → is_decidable (myProd A B)
  | Sum.inl a, Sum.inl b => Sum.inl (myProd.mk a b)
  | Sum.inl _, Sum.inr g => Sum.inr (g ∘ proj2)
  | Sum.inr f, Sum.inl _ => Sum.inr (f ∘ proj1)
  | Sum.inr f, Sum.inr _ => Sum.inr (f ∘ proj1)

def is_decidable_fun {A B : Type} : is_decidable A → is_decidable B → is_decidable (A → B)
  | Sum.inl _, Sum.inl b => Sum.inl (fun _ => b)
  | Sum.inl a, Sum.inr g => Sum.inr (fun h => g (h a))
  | Sum.inr f, Sum.inl _ => Sum.inl (fun a => Empty.elim (f a))
  | Sum.inr f, Sum.inr _ => Sum.inl (fun a => Empty.elim (f a))

-- The negation of a decidable type is decidable.
def is_decidable_neg {A : Type} (d : is_decidable A) : is_decidable (myNegType A) :=
  is_decidable_fun d is_decidable_empty


/- ###################################################################### -/
/-  Example 8.1.4: Eq_ℕ, ≤ and < are decidable                            -/
/- ###################################################################### -/

-- Observational equality on ℕ (Definition 6.3.1; chapter6.lean has it for `N`).
def EqN : myN → myN → Type
  | myN.zero, myN.zero => Unit
  | myN.zero, myN.succ _ => Empty
  | myN.succ _, myN.zero => Empty
  | myN.succ m, myN.succ n => EqN m n

def is_decidable_EqN : (m n : myN) → is_decidable (EqN m n)
  | myN.zero, myN.zero => is_decidable_unit
  | myN.zero, myN.succ _ => is_decidable_empty
  | myN.succ _, myN.zero => is_decidable_empty
  | myN.succ m, myN.succ n => is_decidable_EqN m n

def is_decidable_leq : (m n : myN) → is_decidable (leq m n)
  | myN.zero, _ => is_decidable_unit
  | myN.succ _, myN.zero => is_decidable_empty
  | myN.succ m, myN.succ n => is_decidable_leq m n

def is_decidable_less (m n : myN) : is_decidable (less_than m n) :=
  match m,n with
  | m', myN.zero =>
    match m' with
    | myN.zero => is_decidable_empty
    | myN.succ _ => is_decidable_empty
  | myN.zero, myN.succ _ => is_decidable_unit
  | myN.succ m, myN.succ n => is_decidable_less m n


/- ###################################################################### -/
/-  Definition 8.1.5, Lemma 8.1.6 and Proposition 8.1.7                   -/
/- ###################################################################### -/

-- has-decidable-eq(A) := Π (x y : A), is-decidable(x = y)
abbrev has_decidable_eq (A : Type) : Type := (x y : A) → is_decidable (x ≡ y)

-- Proposition 4.3.4: every map f : A → B induces ¬B → ¬A.
def contrapositive {A B : Type} (f : A → B) : myNegType B → myNegType A :=
  fun g a => g (f a)

-- Remark 4.4.2: the functorial action of +.
def sum_map {A A' B B' : Type} (f : A → A') (g : B → B') : A ⊕ B → A' ⊕ B'
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr (g b)

-- Lemma 8.1.6: if A ↔ B, then A is decidable if and only if B is decidable.
def is_decidable_of_iff {A B : Type} (e : myEquiv A B) : is_decidable A → is_decidable B :=
  sum_map (proj1 e) (contrapositive (proj2 e))

def is_decidable_iff {A B : Type} (e : myEquiv A B) :
    myEquiv (is_decidable A) (is_decidable B) :=
  myProd.mk (is_decidable_of_iff e) (is_decidable_of_iff (myProd.mk (proj2 e) (proj1 e)))

-- Proposition 6.3.3 for myN:  (m = n) ↔ Eq_ℕ(m, n)
def EqN_refl : (n : myN) → EqN n n
  | myN.zero => ()
  | myN.succ n => EqN_refl n

def EqN_of_eq {m n : myN} (p : m ≡ n) : EqN m n :=
  transport (EqN m) p (EqN_refl m)

def eq_of_EqN : (m n : myN) → EqN m n → (m ≡ n)
  | myN.zero, myN.zero, _ => MyEq.refl _
  | myN.zero, myN.succ _, e => Empty.elim e
  | myN.succ _, myN.zero, e => Empty.elim e
  | myN.succ m, myN.succ n, e => ap myN.succ m n (eq_of_EqN m n e)

def eq_iff_EqN (m n : myN) : myEquiv (m ≡ n) (EqN m n) :=
  myProd.mk EqN_of_eq (eq_of_EqN m n)

-- Proposition 8.1.7: equality on the natural numbers is decidable.
def has_decidable_eq_myN : has_decidable_eq myN :=
  fun m n => is_decidable_of_iff (myProd.mk (eq_of_EqN m n) EqN_of_eq) (is_decidable_EqN m n)

-- For later use: m ≠ n is decidable.
def is_decidable_neq (m n : myN) : is_decidable (myNegType (m ≡ n)) :=
  is_decidable_neg (has_decidable_eq_myN m n)


/- ###################################################################### -/
/-  Proposition 8.1.8: the standard finite types have decidable equality   -/
/- ###################################################################### -/

/- The observational equality on `myFin k` (Exercise 7.5).  Recall from
   chapter7.lean that myFin 0 := ∅ and myFin (k+1) := myFin k + 1. -/
def EqFin : (k : myN) → myFin k → myFin k → Type
  | myN.zero, x, _ => Empty.elim x
  | myN.succ k, Sum.inl x, Sum.inl y => EqFin k x y
  | myN.succ _, Sum.inl _, Sum.inr _ => Empty
  | myN.succ _, Sum.inr _, Sum.inl _ => Empty
  | myN.succ _, Sum.inr _, Sum.inr _ => Unit

def EqFin_refl : (k : myN) → (x : myFin k) → EqFin k x x
  | myN.zero, x => Empty.elim x
  | myN.succ k, Sum.inl x => EqFin_refl k x
  | myN.succ _, Sum.inr _ => ()

def EqFin_of_eq {k : myN} {x y : myFin k} (p : x ≡ y) : EqFin k x y :=
  transport (EqFin k x) p (EqFin_refl k x)

def eq_of_EqFin : (k : myN) → (x y : myFin k) → EqFin k x y → (x ≡ y)
  | myN.zero, x, _, _ => Empty.elim x
  | myN.succ k, Sum.inl x, Sum.inl y, e => ap Sum.inl x y (eq_of_EqFin k x y e)
  | myN.succ _, Sum.inl _, Sum.inr _, e => Empty.elim e
  | myN.succ _, Sum.inr _, Sum.inl _, e => Empty.elim e
  | myN.succ _, Sum.inr (), Sum.inr (), _ => MyEq.refl _

def is_decidable_EqFin : (k : myN) → (x y : myFin k) → is_decidable (EqFin k x y)
  | myN.zero, x, _ => Empty.elim x
  | myN.succ k, Sum.inl x, Sum.inl y => is_decidable_EqFin k x y
  | myN.succ _, Sum.inl _, Sum.inr _ => is_decidable_empty
  | myN.succ _, Sum.inr _, Sum.inl _ => is_decidable_empty
  | myN.succ _, Sum.inr _, Sum.inr _ => is_decidable_unit

def has_decidable_eq_Fin (k : myN) : has_decidable_eq (myFin k) :=
  fun x y => is_decidable_of_iff (myProd.mk (eq_of_EqFin k x y) EqFin_of_eq)
                                 (is_decidable_EqFin k x y)

/- Remark: alternatively, we can transfer decidable equality from ℕ along the
   injective map `inclusion : myFin k → myN` of chapter7.lean. -/
example (k : myN) : has_decidable_eq (myFin k) :=
  fun x y => is_decidable_of_iff
               (myProd.mk (inclusion_is_injective k x y) (ap (inclusion k) x y))
               (has_decidable_eq_myN (inclusion k x) (inclusion k y))


/- ###################################################################### -/
/-  Theorem 8.1.9: divisibility is decidable                               -/
/- ###################################################################### -/

/- The book derives Theorem 8.1.9 from Theorem 7.4.7 ((k+1) ∣ x ↔ [x]_{k+1} = 0 in
   Fin_{k+1}), which is not (yet) available in chapter7.lean.  We give a direct
   proof instead: if d ≠ 0 and d · k = n, then k ≤ n, so it suffices to search for
   the witness k among the numbers k ≤ n.  This uses the following lemma, which
   is also part (a) of Exercise 8.10. -/

-- For a decidable family P over ℕ, the type Σ (k : ℕ), (k ≤ n) × P(k) is decidable.
def is_decidable_bounded_sigma (P : myN → Type) (d : is_decidable_family P) :
    (n : myN) → is_decidable (Σ k : myN, myProd (leq k n) (P k))
  | myN.zero =>
      match d myN.zero with
      | Sum.inl p => Sum.inl ⟨myN.zero, myProd.mk () p⟩
      | Sum.inr np =>
          Sum.inr (fun ⟨k, myProd.mk h p⟩ => np (transport P (leq_zero k h) p))
  | myN.succ n =>
      match is_decidable_bounded_sigma P d n with
      | Sum.inl ⟨k, myProd.mk h p⟩ =>
          Sum.inl ⟨k, myProd.mk (leq_trans k n (myN.succ n) h (leq_succ n)) p⟩
      | Sum.inr f =>
          match d (myN.succ n) with
          | Sum.inl p => Sum.inl ⟨myN.succ n, myProd.mk (leq_refl _) p⟩
          | Sum.inr np =>
              Sum.inr (fun ⟨k, myProd.mk h p⟩ =>
                match leq_succ_cases k n h with
                | Sum.inl h' => f ⟨k, myProd.mk h' p⟩
                | Sum.inr e => np (transport P e p))

-- Theorem 8.1.9: for any d, n : ℕ, the type d ∣ n is decidable.
def is_decidable_divides : (d n : myN) → is_decidable (divides d n)
  | myN.zero, n =>
      -- 0 ∣ n holds if and only if n = 0
      is_decidable_of_iff
        (myProd.mk (fun p => ⟨myN.zero, myEq_symm p⟩) (eq_zero_of_zero_divides n))
        (has_decidable_eq_myN n myN.zero)
  | myN.succ d, n =>
      -- (d+1) ∣ n holds if and only if (d+1) · k = n for some k ≤ n
      is_decidable_of_iff
        (myProd.mk
          (fun ⟨k, myProd.mk _ p⟩ => ⟨k, p⟩)
          (fun ⟨k, p⟩ =>
            ⟨k, myProd.mk
                  (transport (fun x => leq k x) ((myMult_comm k (myN.succ d)) • p)
                    (leq_mul_succ_right k d))
                  p⟩))
        (is_decidable_bounded_sigma (fun k => (myN.succ d * k) ≡ n)
          (fun k => has_decidable_eq_myN (myN.succ d * k) n) n)

/- Consequently, the `Prop`-valued divisibility relation `divides` of chapter7.lean
   is decidable in the sense of Lean's `Decidable` class. -/
-- instance decidable_divides (d n : myN) : Decidable (divides d n) :=
--   match is_decidable_divides d n with
--   | Sum.inl p => isTrue (Nonempty.intro p)
--   | Sum.inr np => isFalse (fun ⟨p⟩ => Empty.elim (np p))

end chapter8
