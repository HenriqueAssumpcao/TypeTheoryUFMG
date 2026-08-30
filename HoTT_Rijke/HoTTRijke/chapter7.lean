-- This file contains implementations of congruences and finite types
-- following Chapter 7

import HoTTRijke.chapter2
import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_props_naturals_with_zero
import HoTTRijke.chapter6

open props_naturals_with_zero
open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_propositions
open chapter6_Universes


def divides (d n : myN) : Prop := Nonempty (Σ k : myN, (d * k) ≡ n)

def one_divides_all_n : ∀ n : myN, divides _1 n :=
  fun n => ⟨n, mult_one_left n⟩

def n_divides_n (n : myN) : divides n n := by
  have h : (n * _1) ≡ n := mult_one_right n

  exact ⟨_1, h⟩

def n_divides_zero : ∀ n : myN, divides n myN.zero := sorry

def divides_sum (a n1 n2 : myN) (p : divides a n1) (q : divides a n2) : (divides a (n1 + n2)) := by
  rcases p with ⟨q1,hq1⟩
  rcases q with ⟨q2,hq2⟩
  have t : (a*(q1 + q2)) ≡ (n1 + n2) := by
    calc (a*(q1 + q2)) ≡ ((a*q1) + (a*q2)) := mult_distributive_left a q1 q2
    _ ≡ n1 + (a*q2) := ap (fun x => (x + (a*q2))) (a*q1) n1 hq1
    _  ≡ n1 + n2 := ap (fun x => (n1 + x)) (a*q2) n2 hq2
  exact ⟨q1 + q2, t⟩

def divides_first_summand (a n1 n2 : myN) (p : divides a n2) (q : divides a (n1 + n2)) : divides a n1 := sorry
def divides_second_summand (a n1 n2 : myN) (p : divides a n1) (q : divides a (n1 + n2)) : divides a n2 := sorry


-- The Congruence Relation on N

def cong (x y k : myN) : Prop := divides k (dist x y)

def cong_to_zero (n : myN) : cong n myN.zero n :=
  match n with
  | myN.zero => n_divides_n myN.zero
  | myN.succ n' => n_divides_n n'.succ

def transport_prop {α : Type} {x y : α} (β : (x' : α) → Prop) : (x ≡ y) → (β x → β y) :=
  by
    intro p q
    cases p
    exact q

def cong_refl (x k : myN) : cong x x k := by
  have t : dist x x ≡ myN.zero := dist_equals_0 x
  exact transport_prop (fun n => divides k n) (myEq_symm t) (n_divides_zero k)

def cong_refl_on_equals (x y k : myN) (p : x ≡ y) : cong x y k := by
  exact transport_prop (fun n => divides k n) (myEq_symm (dist_of_equals x y p)) (n_divides_zero k)

def cong_symm (x y k : myN) (p : cong x y k) : cong y x k := by
  have t : dist x y ≡ dist y x := dist_symm x y
  -- divides k dist (x y) -> divides k dist (y x)
  exact transport_prop (fun n => divides k n) t p

def cong_trans (x y z k : myN) (p : cong x y k) (q : cong y z k) : (cong x z k) := by
  rcases (dist_one_of_three x y z) with a | b | c
  -- divides k d(x,y) and divides k d(y,z)  => divides k d(x,y) + d(y,z) => divides k d(x,z)
  · have t : divides k ((dist x y) + (dist y z)) := divides_sum k (dist x y) (dist y z) p q
    exact transport_prop (fun n => divides k n) a t
  ·
    -- b : (dist y z + dist x z) ≡ dist x y
    -- k div d(x,y) = d(y,z) + d(x,z) and k div d(y,z) = > k div(x,z)
    exact divides_second_summand k (dist y z) (dist x z) q
          (transport_prop (fun n => divides k n) (myEq_symm b) p)
  · -- c : (dist x z + dist x y) ≡ dist y z
    exact divides_first_summand k (dist x z) (dist x y) p
      (transport_prop (fun n => divides k n) (myEq_symm c) q)


-- The Standard Finite Types

def myFin (n : myN) : Type :=
  match n with
    | myN.zero => Empty
    | myN.succ n' => Sum (myFin n') Unit




def inclusion (n : myN) (x : myFin n) : myN :=
  match n with
    | myN.zero => Empty.elim x
    | myN.succ n' =>
      match x with
        | Sum.inl x' => inclusion n' x'
        | Sum.inr _ => n'

theorem inclusion_is_bounded (k : myN) : (x : myFin k) → Less_than (inclusion k x) k := by
  intro x
  cases k with
  | zero => exact False.elim (Empty.elim x)
  | succ n' =>
    cases x with
    | inl x' =>
      have h : Less_than (inclusion n'.succ (Sum.inl x')) n' := by
        exact inclusion_is_bounded n' x'
      exact Less_than_trans (inclusion n'.succ (Sum.inl x')) n' n'.succ h (Less_than_succ n')
    | inr _ => exact Less_than_succ n'

def inclusion_is_injective (k : myN) (x y : myFin k) : (inclusion k x ≡ inclusion k y) → (x ≡ y) := by
  cases k with
  | zero => exact fun p => Empty.elim x
  | succ k' =>
    intro p
    cases x with
    | inl x' =>
      cases y with
      | inl y' => exact ap (Sum.inl) _ _ (inclusion_is_injective k' x' y' p)
      | inr _ => exact False.elim (Less_than_on_equals _ _ p (inclusion_is_bounded k' x'))
    | inr _ =>
      cases y with
      | inl y' => exact False.elim (Less_than_on_equals _ _ (myEq_symm p) (inclusion_is_bounded k' y'))
      | inr _ => exact MyEq.refl _


-- The natural numbers modulo 𝑘 + 1

def zero (k : myN) : myFin k.succ := by
  match k with
  | myN.zero => exact Sum.inr ()
  | myN.succ k' => exact Sum.inl (zero k')


def skip_zero (k : myN) (x : myFin k) : myFin k.succ := by
  match k with
  | myN.zero => exact Sum.inr ()
  | myN.succ k' =>
    match x with
    | Sum.inl x' => exact Sum.inl (skip_zero k' x')
    | Sum.inr _ => exact Sum.inr ()


def succ_fin (k : myN) (x : myFin k) : myFin k :=
  match k with
  | myN.zero => Empty.elim x
  | myN.succ k' =>
    match x with
    | Sum.inl x' => skip_zero k' x'
    | Sum.inr _ => zero k'

def quotient_map (k : myN) (n : myN) : myFin k.succ := by
  match n with
  | myN.zero => exact zero k
  | myN.succ n' => exact succ_fin k.succ (quotient_map k n')


-- Lemma 7.4.4 (i)
-- inclusion(zero) = 0

def inclusion_zero_eq_zero (k : myN): (inclusion k.succ (zero k)) ≡ myN.zero := by
  match k with
  | myN.zero => exact MyEq.refl _
  | myN.succ k' => exact inclusion_zero_eq_zero k'

-- (ii)
-- inclusion(skip_zero(x)) = inclusion(x) + 1

def inclusion_skip_zero_eq_succ (k : myN) (x : myFin k) : (inclusion k.succ (skip_zero k x)) ≡ (myN.succ (inclusion k x)) := by
  match k with
  | myN.zero => exact Empty.elim x
  | myN.succ k' =>
    match x with
    | Sum.inl x' => exact inclusion_skip_zero_eq_succ k' x'
    | Sum.inr _ => exact MyEq.refl _


-- (iii)
-- inclusion(succ_fin(x)) = inclusion(x) + 1

theorem inclusion_succ_fin_eq_succ (k : myN) (x : myFin k) : cong (inclusion k (succ_fin k x)) (myN.succ (inclusion k x)) k := by
  match k with
  | myN.zero => exact Empty.elim x
  | myN.succ k' =>
    match x with
    | Sum.inl x' =>
      have h : inclusion k'.succ (succ_fin k'.succ (Sum.inl x')) ≡ inclusion k'.succ (skip_zero k' x') := by
        exact MyEq.refl _
      have h2 : inclusion k'.succ (skip_zero k' x') ≡ myN.succ (inclusion k'.succ (Sum.inl x')) := by
        exact inclusion_skip_zero_eq_succ k' x'

      exact cong_refl_on_equals _ _ k'.succ (h • h2)

    | Sum.inr _ =>
      have h : inclusion k'.succ (succ_fin k'.succ (Sum.inr _)) ≡ myN.zero :=
        calc
          inclusion k'.succ (succ_fin k'.succ (Sum.inr ())) ≡ inclusion k'.succ (zero k') := MyEq.refl _
          _ ≡ myN.zero := inclusion_zero_eq_zero k'

      have h1 : cong myN.zero k'.succ k'.succ := cong_to_zero k'.succ
      have h2 : cong (inclusion k'.succ (succ_fin k'.succ (Sum.inr _))) k'.succ k'.succ :=
        cong_trans _ _ _ _ (cong_refl_on_equals _ _ _ h) h1

      have h3 : k'.succ ≡ myN.succ (inclusion k'.succ (Sum.inr ())) := MyEq.refl _

      exact cong_trans _ _ _ _ h2 (cong_refl_on_equals _ _ _ h3)
