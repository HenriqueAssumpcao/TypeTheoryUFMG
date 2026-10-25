-- This file contains implementations of congruences and finite types
-- following Chapter 7

import HoTTRijke.chapter2
import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter4
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_props_naturals_with_zero
import HoTTRijke.chapter6

open chapter3_naturals_with_zero
open chapter4_coproducts
open chapter5_myeq
open props_naturals_with_zero
open chapter6_Universes


def divides (d n : myN) : Type := Σ k : myN, (d × k) ≡ n

def one_divides_all_n : ∀ n : myN, divides _1 n :=
  fun n => ⟨n, mult_one_left n⟩

def n_divides_n (n : myN) : divides n n := by
  have h : (n * _1) ≡ n := mult_one_right n

  exact ⟨_1, h⟩

def divides_sum (a n1 n2 : myN) (p : divides a n1) (q : divides a n2) : (divides a (n1 + n2)) := by
  rcases p with ⟨q1,hq1⟩
  rcases q with ⟨q2,hq2⟩
  have t : (a*(q1 + q2)) ≡ (n1 + n2) := by
    calc (a*(q1 + q2)) ≡ ((a*q1) + (a*q2)) := mult_distributive_left a q1 q2
    _ ≡ n1 + (a*q2) := ap (fun x => (x + (a*q2))) (a*q1) n1 hq1
    _  ≡ n1 + n2 := ap (fun x => (n1 + x)) (a*q2) n2 hq2
  exact ⟨q1 + q2, t⟩


def divides_add_left (d x y : myN) (p : divides d x) (q : divides d (myAdd x y)) : divides d y := by
  rcases p with ⟨a, ha⟩
  rcases q with ⟨b, hb⟩
  cases leq_total a b with
  | inl h =>
      have e : (myAdd x (d * dist a b)) ≡ (myAdd x y) :=
        ap (fun t => myAdd t (d * dist a b)) _ _ (myEq_symm ha) •
        myEq_symm (mult_distributive_left d a (dist a b)) •
        ap (myMult d) _ _ (add_dist_of_leq a b h) • hb
      exact ⟨dist a b, add_nat_injective
        (myAdd_commutative _ _ • e • myAdd_commutative _ _)⟩
  | inr h =>
      have e : (myAdd (myAdd x y) (d * dist b a)) ≡ x :=
        ap (fun t => myAdd t (d * dist b a)) _ _ (myEq_symm hb) •
        myEq_symm (mult_distributive_left d b (dist b a)) •
        ap (myMult d) _ _ (add_dist_of_leq b a h) • ha
      have z : (myAdd y (d * dist b a)) ≡ myN.zero :=
        add_nat_injective (myAdd_commutative _ _ •
          myEq_symm (myAdd_associative x y (d * dist b a)) • e •
          myEq_symm (myAdd_zero_left x))
      exact ⟨myN.zero, myEq_symm (chapter3_booleans.proj1 (sum_equals_zero z))⟩
def divides_add_right (d x y : myN) (p : divides d y) (q : divides d (myAdd x y)) : divides d x :=
  divides_add_left d y x p ⟨q.1, q.2 • myAdd_commutative x y⟩



-- The Congruence Relation on N

def cong (x y k : myN) : Type := divides k (dist x y)

def cong_to_zero (n : myN) : cong n myN.zero n :=
  match n with
  | myN.zero => n_divides_n myN.zero
  | myN.succ n' => n_divides_n n'.succ


def cong_refl (x k : myN) : cong x x k :=
  have h : dist x x ≡ _0 := dist_equals_0 x
  have p (k : myN) : (k × _0) ≡ dist x x := (myMult_comm _ _) • (myMult_zero_left k) • myEq_symm h
  ⟨_0, p k⟩

def cong_refl_on_equals (x y k : myN) (p : x ≡ y) : cong x y k :=
  have h : dist x y ≡ _0 := dist_equals _ _ p
  have p (k : myN) : (k × _0) ≡ dist x y := (myMult_comm _ _) • (myMult_zero_left k) • myEq_symm h
  ⟨_0, p k⟩


def cong_symm (x y k : myN) (p : cong x y k) : cong y x k :=
  ⟨p.1, p.2 • dist_commutative _ _⟩

def cong_trans (x y z k : myN) (p : cong x y k) (q : cong y z k) : cong x z k := by
  let hdist := dist_transitivity x y z

  match hdist with
  | mySum.inl h =>
      -- dist(x,y) + dist(y,z) = dist(x,z)
      have h' : divides k (myAdd (dist x y) (dist y z)) :=
        divides_sum k (dist x y) (dist y z) ⟨p.1, p.2⟩ ⟨q.1, q.2⟩

      exact ⟨h'.1, h'.2 • h⟩

  | mySum.inr (mySum.inl h) =>
      -- dist(y,z) + dist(x,z) = dist(x,y)
      have h' : divides k (myAdd (dist y z) (dist x z)) := ⟨p.1, p.2 • (myEq_symm h)⟩
      have h1 : divides k (dist x z) := divides_add_left k _ _ q h'

      exact h1

  | mySum.inr (mySum.inr h) =>
      -- dist(x,z) + dist(x,y) = dist(y,z)
      have h' : divides k (myAdd (dist x z) (dist x y)) := ⟨q.1, q.2 • (myEq_symm h)⟩
      have h1 : divides k (dist x z) := divides_add_right k _ _ p h'

      exact h1

def cong_succ (x y k : myN) (p : cong x y k) : cong (myN.succ x) (myN.succ y) k :=
  have h : dist (myN.succ x) (myN.succ y) ≡ dist x y := MyEq.refl _
  ⟨p.1, p.2 • h⟩


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

def inclusion_is_bounded (k : myN) : (x : myFin k) → less_than (inclusion k x) k := by
  intro x
  cases k with
  | zero => exact False.elim (Empty.elim x)
  | succ n' =>
    cases x with
    | inl x' =>
      have h : less_than (inclusion n'.succ (Sum.inl x')) n' := by
        exact inclusion_is_bounded n' x'
      exact less_than_trans (inclusion n'.succ (Sum.inl x')) n' n'.succ h (less_than_succ n')
    | inr _ => exact less_than_succ n'

def inclusion_is_injective (k : myN) (x y : myFin k) : (inclusion k x ≡ inclusion k y) → (x ≡ y) := by
  cases k with
  | zero => exact fun p => Empty.elim x
  | succ k' =>
    intro p
    cases x with
    | inl x' =>
      cases y with
      | inl y' => exact ap (Sum.inl) _ _ (inclusion_is_injective k' x' y' p)
      | inr _ => exact Empty.elim (less_than_on_equals _ _ p (inclusion_is_bounded k' x'))
    | inr _ =>
      cases y with
      | inl y' => exact Empty.elim (less_than_on_equals _ _ (myEq_symm p) (inclusion_is_bounded k' y'))
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

def inclusion_succ_fin_eq_succ (k : myN) (x : myFin k) : cong (inclusion k (succ_fin k x)) (myN.succ (inclusion k x)) k := by
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


-- Proposition 7.4.5
-- i([x]_k+1) ≡ x mod (k + 1)

def inclusion_quotient_map_cong (k x : myN) : cong (inclusion k.succ (quotient_map k x)) x k.succ := by
  match x with
  | myN.zero => exact cong_refl_on_equals _ _ _ (inclusion_zero_eq_zero k)
  | myN.succ n' =>
    have h : cong (inclusion k.succ (succ_fin k.succ (quotient_map k n'))) (myN.succ (inclusion k.succ (quotient_map k n'))) k.succ :=
      inclusion_succ_fin_eq_succ k.succ (quotient_map k n')

    have h2 : cong (myN.succ (inclusion k.succ (quotient_map k n'))) (myN.succ n') k.succ := by
      exact cong_succ _ _ _ (inclusion_quotient_map_cong k n')
    exact cong_trans _ _ _ _ h h2


-- Proposition 7.4.6
-- if x < d, then d|x <=> x = 0

def divides_less (d x : myN) (p : less_than x d) (q : divides d x) :  (x ≡ myN.zero) := by
  rcases q with ⟨n, h⟩
  cases n with
  | zero => exact myEq_symm h
  | succ n =>
      have hd : leq d (d * n.succ) :=
        transport (fun t => leq t (d * n.succ)) (mult_one_left d)
          (transport (leq (_1 * d)) (myMult_comm n.succ d)
            (mult_succ_leq _1 n.succ d ()))
      have hdx : leq d x := transport (leq d) h hd
      exact Empty.elim (less_than_on_equals x d
        (leq_antisymm x d (less_than_leq x d p) hdx) p)

/- Finite cyclic operations used in Example 9.2.5.
   All identities below are constructed directly on myFin, independently of
   the divisibility results above. -/

-- Decompose an element into zero or a successor without wraparound.
def split_zero_fin : (k : myN) → myFin k.succ → Unit ⊕ myFin k
  | myN.zero, Sum.inl e => nomatch e
  | myN.zero, Sum.inr () => Sum.inl ()
  | myN.succ k, Sum.inl x =>
      match split_zero_fin k x with
      | Sum.inl () => Sum.inl ()
      | Sum.inr y => Sum.inr (Sum.inl y)
  | myN.succ _, Sum.inr () => Sum.inr (Sum.inr ())

def split_zero_fin_zero : (k : myN) → split_zero_fin k (zero k) ≡ Sum.inl ()
  | myN.zero => MyEq.refl _
  | myN.succ k => ap (fun s : Unit ⊕ myFin k => (match s with
      | Sum.inl () => Sum.inl ()
      | Sum.inr y => Sum.inr (Sum.inl y) : Unit ⊕ myFin k.succ)) _ _ (split_zero_fin_zero k)

def split_zero_fin_skip : (k : myN) → (x : myFin k) →
    split_zero_fin k (skip_zero k x) ≡ Sum.inr x
  | myN.zero, e => nomatch e
  | myN.succ k, Sum.inl x => ap (fun s : Unit ⊕ myFin k => (match s with
      | Sum.inl () => Sum.inl ()
      | Sum.inr y => Sum.inr (Sum.inl y) : Unit ⊕ myFin k.succ)) _ _ (split_zero_fin_skip k x)
  | myN.succ _, Sum.inr () => MyEq.refl _

def join_zero_fin (k : myN) : Unit ⊕ myFin k → myFin k.succ
  | Sum.inl () => zero k
  | Sum.inr x => skip_zero k x

def join_split_zero_fin : (k : myN) → (x : myFin k.succ) →
    join_zero_fin k (split_zero_fin k x) ≡ x
  | myN.zero, Sum.inl e => nomatch e
  | myN.zero, Sum.inr () => MyEq.refl _
  | myN.succ k, Sum.inl x => by
      have commute (t : Unit ⊕ myFin k) :
          join_zero_fin k.succ (match t with
            | Sum.inl () => Sum.inl ()
            | Sum.inr y => Sum.inr (Sum.inl y)) ≡
          Sum.inl (join_zero_fin k t) := by
        cases t with
        | inl u => cases u; exact MyEq.refl _
        | inr y => exact MyEq.refl _
      exact commute (split_zero_fin k x) • ap Sum.inl _ _ (join_split_zero_fin k x)
  | myN.succ _, Sum.inr () => MyEq.refl _

-- A dependent eliminator in zero/skip-zero coordinates.
def ind_zero_fin (k : myN) (P : myFin k.succ → Type)
    (z : P (zero k)) (s : (x : myFin k) → P (skip_zero k x))
    (x : myFin k.succ) : P x :=
  transport P (join_split_zero_fin k x)
    (match split_zero_fin k x with | Sum.inl () => z | Sum.inr y => s y)

def pred_fin : (k : myN) → myFin k → myFin k
  | myN.zero, e => nomatch e
  | myN.succ k, x => match split_zero_fin k x with
      | Sum.inl () => Sum.inr ()
      | Sum.inr y => Sum.inl y

def pred_fin_zero (k : myN) : pred_fin k.succ (zero k) ≡ Sum.inr () :=
  ap (fun s => match s with | Sum.inl () => Sum.inr () | Sum.inr y => Sum.inl y)
    _ _ (split_zero_fin_zero k)

def pred_fin_skip (k : myN) (x : myFin k) :
    pred_fin k.succ (skip_zero k x) ≡ Sum.inl x :=
  ap (fun s => match s with | Sum.inl () => Sum.inr () | Sum.inr y => Sum.inl y)
    _ _ (split_zero_fin_skip k x)

def pred_succ_fin : (k : myN) → (x : myFin k) → pred_fin k (succ_fin k x) ≡ x
  | myN.zero, e => nomatch e
  | myN.succ k, Sum.inl x => pred_fin_skip k x
  | myN.succ k, Sum.inr () => pred_fin_zero k

def succ_pred_fin : (k : myN) → (x : myFin k) → succ_fin k (pred_fin k x) ≡ x
  | myN.zero, e => nomatch e
  | myN.succ k, x => ind_zero_fin k (fun x => succ_fin k.succ (pred_fin k.succ x) ≡ x)
      (ap (succ_fin k.succ) _ _ (pred_fin_zero k))
      (fun y => ap (succ_fin k.succ) _ _ (pred_fin_skip k y)) x

-- Translation by a natural number, forwards and backwards around the cycle.
def add_nat_fin (k : myN) : myN → myFin k → myFin k
  | myN.zero, x => x
  | myN.succ n, x => succ_fin k (add_nat_fin k n x)

def sub_nat_fin (k : myN) : myN → myFin k → myFin k
  | myN.zero, x => x
  | myN.succ n, x => sub_nat_fin k n (pred_fin k x)

def add_sub_nat_fin (k : myN) : (n : myN) → (x : myFin k) →
    add_nat_fin k n (sub_nat_fin k n x) ≡ x
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x =>
      ap (succ_fin k) _ _ (add_sub_nat_fin k n (pred_fin k x)) • succ_pred_fin k x

def sub_add_nat_fin (k : myN) : (n : myN) → (x : myFin k) →
    sub_nat_fin k n (add_nat_fin k n x) ≡ x
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x =>
      ap (sub_nat_fin k n) _ _ (pred_succ_fin k (add_nat_fin k n x)) • sub_add_nat_fin k n x

-- Addition and subtraction by the canonical representative of the second input.
def add_fin (k : myN) (x a : myFin k) : myFin k := add_nat_fin k (inclusion k a) x

def sub_fin (k : myN) (x a : myFin k) : myFin k := sub_nat_fin k (inclusion k a) x

def add_sub_fin (k : myN) (x a : myFin k) : add_fin k (sub_fin k x a) a ≡ x :=
  add_sub_nat_fin k (inclusion k a) x

def sub_add_fin (k : myN) (x a : myFin k) : sub_fin k (add_fin k x a) a ≡ x :=
  sub_add_nat_fin k (inclusion k a) x

-- Reflection of the ordered finite interval: i maps to k - 1 - i.
def reverse_fin : (k : myN) → myFin k → myFin k
  | myN.zero, e => nomatch e
  | myN.succ k, Sum.inl x => skip_zero k (reverse_fin k x)
  | myN.succ k, Sum.inr () => zero k

def reverse_fin_zero : (k : myN) → reverse_fin k.succ (zero k) ≡ Sum.inr ()
  | myN.zero => MyEq.refl _
  | myN.succ k => ap (skip_zero k.succ) _ _ (reverse_fin_zero k)

def reverse_fin_skip : (k : myN) → (x : myFin k) →
    reverse_fin k.succ (skip_zero k x) ≡ Sum.inl (reverse_fin k x)
  | myN.zero, e => nomatch e
  | myN.succ k, Sum.inl x => ap (skip_zero k.succ) _ _ (reverse_fin_skip k x)
  | myN.succ _, Sum.inr () => MyEq.refl _

def reverse_fin_involutive : (k : myN) → (x : myFin k) →
    reverse_fin k (reverse_fin k x) ≡ x
  | myN.zero, e => nomatch e
  | myN.succ k, Sum.inl x =>
      reverse_fin_skip k (reverse_fin k x) • ap Sum.inl _ _ (reverse_fin_involutive k x)
  | myN.succ k, Sum.inr () => reverse_fin_zero k

def reverse_succ_fin : (k : myN) → (x : myFin k) →
    reverse_fin k (succ_fin k x) ≡ pred_fin k (reverse_fin k x)
  | myN.zero, e => nomatch e
  | myN.succ k, Sum.inl x =>
      reverse_fin_skip k x • myEq_symm (pred_fin_skip k (reverse_fin k x))
  | myN.succ k, Sum.inr () => reverse_fin_zero k • myEq_symm (pred_fin_zero k)

-- Modular negation is the successor of the interval reflection.
def neg_fin (k : myN) (x : myFin k) : myFin k := succ_fin k (reverse_fin k x)

def neg_fin_involutive (k : myN) (x : myFin k) : neg_fin k (neg_fin k x) ≡ x :=
  ap (succ_fin k) _ _ (reverse_succ_fin k (reverse_fin k x)) •
  succ_pred_fin k (reverse_fin k (reverse_fin k x)) • reverse_fin_involutive k x

def neg_fin_zero (k : myN) : neg_fin k.succ (zero k) ≡ zero k :=
  ap (succ_fin k.succ) _ _ (reverse_fin_zero k)

-- Induction along the interval, without a cyclic step at the last element.
def ind_fin_order : (k : myN) → (P : myFin k.succ → Type) →
    P (zero k) → ((x : myFin k) → P (Sum.inl x) → P (skip_zero k x)) →
    (x : myFin k.succ) → P x
  | myN.zero, _, _, _, Sum.inl e => nomatch e
  | myN.zero, _, z, _, Sum.inr () => z
  | myN.succ k, P, z, s, Sum.inl x =>
      ind_fin_order k (fun y => P (Sum.inl y)) z (fun y h => s (Sum.inl y) h) x
  | myN.succ k, P, z, s, Sum.inr () =>
      s (Sum.inr ())
        (ind_fin_order k (fun y => P (Sum.inl y)) z (fun y h => s (Sum.inl y) h) (Sum.inr ()))

def add_nat_fin_zero_inclusion (k : myN) (x : myFin k.succ) :
    add_nat_fin k.succ (inclusion k.succ x) (zero k) ≡ x :=
  ind_fin_order k (fun x => add_nat_fin k.succ (inclusion k.succ x) (zero k) ≡ x)
    (ap (fun n => add_nat_fin k.succ n (zero k)) _ _ (inclusion_zero_eq_zero k))
    (fun y h =>
      ap (fun n => add_nat_fin k.succ n (zero k)) _ _ (inclusion_skip_zero_eq_succ k y) •
      ap (succ_fin k.succ) _ _ h) x

def neg_succ_fin (k : myN) (x : myFin k) :
    neg_fin k (succ_fin k x) ≡ pred_fin k (neg_fin k x) :=
  ap (succ_fin k) _ _ (reverse_succ_fin k x) •
  succ_pred_fin k (reverse_fin k x) • myEq_symm (pred_succ_fin k (reverse_fin k x))

def sub_nat_fin_pred (k : myN) : (n : myN) → (x : myFin k) →
    sub_nat_fin k n (pred_fin k x) ≡ pred_fin k (sub_nat_fin k n x)
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x => sub_nat_fin_pred k n (pred_fin k x)

def neg_add_nat_fin (k : myN) : (n : myN) → (x : myFin k) →
    neg_fin k (add_nat_fin k n x) ≡ sub_nat_fin k n (neg_fin k x)
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x => neg_succ_fin k (add_nat_fin k n x) •
      ap (pred_fin k) _ _ (neg_add_nat_fin k n x) •
      myEq_symm (sub_nat_fin_pred k n (neg_fin k x))

-- The reflection definition agrees with subtraction from zero.
def neg_fin_eq_sub (k : myN) (a : myFin k.succ) :
    neg_fin k.succ a ≡ sub_fin k.succ (zero k) a :=
  myEq_symm (ap (neg_fin k.succ) _ _ (add_nat_fin_zero_inclusion k a)) •
  neg_add_nat_fin k.succ (inclusion k.succ a) (zero k) •
  ap (sub_nat_fin k.succ (inclusion k.succ a)) _ _ (neg_fin_zero k)

def add_fin_left_inverse (k : myN) (a : myFin k.succ) :
    add_fin k.succ (neg_fin k.succ a) a ≡ zero k :=
  ap (fun x => add_fin k.succ x a) _ _ (neg_fin_eq_sub k a) •
  add_sub_fin k.succ (zero k) a

def add_nat_fin_succ (k : myN) : (n : myN) → (x : myFin k) →
    add_nat_fin k n (succ_fin k x) ≡ succ_fin k (add_nat_fin k n x)
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x => ap (succ_fin k) _ _ (add_nat_fin_succ k n x)

def add_nat_fin_comm (k : myN) : (n m : myN) → (x : myFin k) →
    add_nat_fin k n (add_nat_fin k m x) ≡ add_nat_fin k m (add_nat_fin k n x)
  | myN.zero, _, _ => MyEq.refl _
  | myN.succ n, m, x => ap (succ_fin k) _ _ (add_nat_fin_comm k n m x) •
      myEq_symm (add_nat_fin_succ k m (add_nat_fin k n x))

def add_fin_comm : (k : myN) → (x a : myFin k) → add_fin k x a ≡ add_fin k a x
  | myN.zero, e, _ => nomatch e
  | myN.succ k, x, a =>
      ap (add_nat_fin k.succ (inclusion k.succ a)) _ _
        (myEq_symm (add_nat_fin_zero_inclusion k x)) •
      add_nat_fin_comm k.succ (inclusion k.succ a) (inclusion k.succ x) (zero k) •
      ap (add_nat_fin k.succ (inclusion k.succ x)) _ _ (add_nat_fin_zero_inclusion k a)

def add_fin_assoc (k : myN) (x a b : myFin k) :
    add_fin k (add_fin k x a) b ≡ add_fin k x (add_fin k a b) :=
  ap (fun y => add_fin k y b) _ _ (add_fin_comm k x a) •
  add_nat_fin_comm k (inclusion k b) (inclusion k x) a •
  add_fin_comm k (add_fin k a b) x

def add_fin_zero_right (k : myN) (x : myFin k.succ) :
    add_fin k.succ x (zero k) ≡ x :=
  ap (fun n => add_nat_fin k.succ n x) _ _ (inclusion_zero_eq_zero k)

def add_fin_right_inverse (k : myN) (a : myFin k.succ) :
    add_fin k.succ a (neg_fin k.succ a) ≡ zero k :=
  add_fin_comm k.succ a (neg_fin k.succ a) • add_fin_left_inverse k a

def add_fin_cancel_neg : (k : myN) → (x a : myFin k) →
    add_fin k (add_fin k x a) (neg_fin k a) ≡ x
  | myN.zero, e, _ => nomatch e
  | myN.succ k, x, a => add_fin_assoc k.succ x a (neg_fin k.succ a) •
      ap (add_fin k.succ x) _ _ (add_fin_right_inverse k a) • add_fin_zero_right k x

def add_fin_cancel_neg_left : (k : myN) → (x a : myFin k) →
    add_fin k (add_fin k x (neg_fin k a)) a ≡ x
  | myN.zero, e, _ => nomatch e
  | myN.succ k, x, a => add_fin_assoc k.succ x (neg_fin k.succ a) a •
      ap (add_fin k.succ x) _ _ (add_fin_left_inverse k a) • add_fin_zero_right k x
