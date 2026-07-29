import HoTTRijke.chapter2
import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_props_naturals_with_zero

open props_naturals_with_zero
open chapter5_myeq
open chapter3_naturals_with_zero


def divides (d n : myN) : Prop := Nonempty (Σ k : myN, (d * k) ≡ n)

def one_divides_all_n : ∀ n : myN, divides _1 n :=
  fun n => ⟨n, mult_one_left n⟩

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

def cong (x y k : myN) : Prop := divides k (dist x y)

def transport_prop {α : Type} {x y : α} (β : (x' : α) → Prop) : (x ≡ y) → (β x → β y) :=
  by
    intro p q
    cases p
    exact q

def cong_refl (x k : myN) : cong x x k := by
  have t : dist x x ≡ myN.zero := dist_equals_0 x
  exact transport_prop (fun n => divides k n) (myEq_symm t) (n_divides_zero k)

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


def myFin (n : myN) : Type :=
  match n with
    | myN.zero => Empty
    | myN.succ n' => Sum (myFin n') Unit
