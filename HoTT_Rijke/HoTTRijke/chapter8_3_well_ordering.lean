/-
  Chapter 8.3 — The well-ordering principle of ℕ

  Every decidable family over ℕ that is inhabited at some n has a least element.
-/

import HoTTRijke.chapter8_2_case_analysis

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans

namespace chapter8

/- ###################################################################### -/
/-  Definition 8.3.1                                                       -/
/- ###################################################################### -/

-- (i)  n is a lower bound for P:  Π (x : ℕ), P(x) → (n ≤ x)
abbrev is_lower_bound (P : myN → Type) (n : myN) : Type := (x : myN) → P x → leqN n x

-- (ii) n is an upper bound for P:  Π (x : ℕ), P(x) → (x ≤ n)
abbrev is_upper_bound (P : myN → Type) (n : myN) : Type := (x : myN) → P x → leqN x n

-- A minimal element of P is an element of P that is also a lower bound for P.
abbrev minimal_element (P : myN → Type) : Type :=
  Σ m : myN, myProd (P m) (is_lower_bound P m)


/- ###################################################################### -/
/-  Theorem 8.3.2: the well-ordering principle of ℕ                        -/
/- ###################################################################### -/

/- As in the book, we prove by induction on n that P(n) → Σ (m : ℕ), P(m) ×
   is-lower-bound_P(m) holds for every decidable family P (the strengthened
   induction hypothesis quantifies over all decidable families). -/
def well_ordering_principle_aux : (n : myN) → (P : myN → Type) →
    is_decidable_family P → P n → minimal_element P
  -- Base case: 0 is a lower bound of every family over ℕ.
  | myN.zero, _, _, p => ⟨myN.zero, myProd.mk p (fun _ _ => ())⟩
  | myN.succ n, P, d, p =>
      match d myN.zero with
      -- If P(0) holds, then 0 is minimal.
      | Sum.inl p0 => ⟨myN.zero, myProd.mk p0 (fun _ _ => ())⟩
      -- If ¬P(0), we find a minimal element m of P'(x) := P(x + 1);
      -- then m + 1 is a minimal element of P.
      | Sum.inr np0 =>
          match well_ordering_principle_aux n (fun x => P (myN.succ x))
                  (fun x => d (myN.succ x)) p with
          | ⟨m, myProd.mk pm lb⟩ =>
              ⟨myN.succ m, myProd.mk pm (fun x px =>
                match x, px with
                | myN.zero, px => Empty.elim (np0 px)
                | myN.succ x, px => lb x px)⟩

-- Theorem 8.3.2
def well_ordering_principle (P : myN → Type) (d : is_decidable_family P) :
    (Σ n : myN, P n) → minimal_element P
  | ⟨n, p⟩ => well_ordering_principle_aux n P d p


-- Minimal elements are unique.
def minimal_element_unique (P : myN → Type) (m m' : myN)
    (H : myProd (P m) (is_lower_bound P m)) (H' : myProd (P m') (is_lower_bound P m')) :
    m ≡ m' :=
  leqN_antisymm m m' (proj2 H m' (proj1 H')) (proj2 H' m (proj1 H))


-- Example: the least number n with 3 ≤ n + n is 2.
example : (well_ordering_principle (fun n => leqN _3 (n + n))
            (fun n => is_decidable_leqN _3 (n + n)) ⟨_3, ()⟩).1 ≡ _2 :=
  MyEq.refl _

end chapter8
