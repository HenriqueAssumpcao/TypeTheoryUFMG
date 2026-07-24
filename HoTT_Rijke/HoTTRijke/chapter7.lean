import HoTTRijke.chapter2
import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_props_naturals_with_zero

open props_naturals_with_zero
open chapter5_myeq
open chapter3_naturals_with_zero

#check myN

def divides (d n : myN) : Prop := Nonempty (Σ k : myN, (d * k) ≡ n)

def one_divides_all_n : ∀ n : myN, divides _1 n :=
  fun n => ⟨n, mult_one_left n⟩

def all_n_divides_zero : ∀ n : myN, divides n _0 :=
  fun n => ⟨_0, mult_zero_right n⟩

def sum_divides_n (a n1 n2 : myN) (p : divides a n1) (q : divides a n2) : (divides a (n1 + n2)) := by
  rcases p with ⟨q1,hq1⟩
  rcases q with ⟨q2,hq2⟩
  have t : (a*(q1 + q2)) ≡ (n1 + n2) := by
    calc
    (a*(q1 + q2)) ≡ ((a*q1) + (a*q2)) := mult_distributive_left a q1 q2
    _ ≡ n1 + (a*q2) := ap (fun x => (x + (a*q2))) (a*q1) n1 hq1
    _  ≡ n1 + n2 := ap (fun x => (n1 + x)) (a*q2) n2 hq2
  exact ⟨q1 + q2, t⟩



-- The congruence relations on ℕ

def congruence (n1 n2 k : myN) : Prop := divides k (dist n1 n2)

def congruent_to_0 (k : myN) : congruence k _0 k :=
  match k with
  | myN.zero => ⟨_0, mult_zero_right _0⟩
  | myN.succ k' => ⟨_1, mult_one_right (myN.succ k')⟩

def congruence_refl (n k : myN) : congruence n n k :=
  have h : (k * _0) ≡ dist n n :=  mult_zero_right k • myEq_symm (dist_equals_0 n)
  ⟨_0, h⟩

def congruence_symm (n1 n2 k : myN) : congruence n1 n2 k → congruence n2 n1 k :=
  fun h => match h with
  | ⟨q, hq⟩ => ⟨q, hq • dist_symm n1 n2⟩





-- def congruence_trans (n1 n2 n3 k : myN) : congruence n1 n2 k → congruence n2 n3 k → congruence n1 n3 k :=
--   fun h1 h2 => match h1 with
--   | ⟨q1, hq1⟩ => match h2 with
--     | ⟨q2, hq2⟩ =>
--       have t : (k * (q1 + q2)) ≡ dist n1 n3 := by
--         calc
--         (k * (q1 + q2)) ≡ ((k * q1) + (k * q2)) := mult_distributive_left k q1 q2
--         _ ≡ dist n1 n2 + (k * q2) := ap (fun x => x + (k * q2)) (k * q1) (dist n1 n2) hq1
--         _ ≡ dist n1 n2 + dist n2 n3 := ap (fun x => dist n1 n2 + x) (k * q2) (dist n2 n3) hq2
--         _ ≡ dist n1 n3 := sorry
--       ⟨q1 + q2, t⟩
