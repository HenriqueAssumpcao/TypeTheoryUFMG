import HoTTRijke.chapter2
import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_ints
import HoTTRijke.chapter6

open chapter3_naturals
open chapter5_myeq

def divides (d n : myN) : Prop := Nonempty (Σ k : myN, (myMult d k) ≡ n)

def one_divides_all_n : ∀ n : myN, divides _1 n :=
  fun n => ⟨n, Naturals.mult_one_left n⟩
