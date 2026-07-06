import HoTTRijke.chapter2
import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_ints
import HoTTRijke.chapter6

open chapter3_naturals
open chapter5_myeq
open Naturals

def divides (d n : myN) : Prop := Nonempty (Σ k : myN, (d * k) ≡ n)

def one_divides_all_n : ∀ n : myN, divides _1 n :=
  fun n => ⟨n, Naturals.mult_one_left n⟩

def sum_divides_n (a n1 n2 : myN) (p : divides a n1) (q : divides a n2) : (divides a (n1 + n2)) := by
  rcases p with ⟨q1,hq1⟩
  rcases q with ⟨q2,hq2⟩
  have t : (a*(q1 + q2)) ≡ (n1 + n2) := by
    calc (a*(q1 + q2)) ≡ ((a*q1) + (a*q2)) := mult_distributive_left a q1 q2
    _ ≡ n1 + n2 := sorry
  exact ⟨q1 + q2, t⟩
