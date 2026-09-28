/-
  Chapter 8.2 — Constructions by case analysis

  To define a function by case analysis on whether a decidable type holds, we first
  define it on an arbitrary element of is-decidable(A) (by the induction principle of
  coproducts) and then substitute the given decision.  This is illustrated with the
  Collatz function (Definition 8.2.1) and "with-abstraction" (Remark 8.2.2), and it
  is used to prove improved closure properties of decidable types
  (Proposition 8.2.3, Proposition 8.2.4 and Corollary 8.2.5).
-/

import HoTTRijke.chapter8_1_decidability

open chapter5_myeq
open chapter3_naturals_with_zero
open chapter3_booleans

namespace chapter8

/- ###################################################################### -/
/-  Definition 8.2.1: the Collatz function                                 -/
/- ###################################################################### -/

-- (i)  h(n, inl(k, p)) := k   and   h(n, inr f) := 3n + 1
def collatz_h (n : myN) : is_decidable (divides _2 n) → myN
  | Sum.inl ⟨k, _⟩ => k
  | Sum.inr _ => (_3 * n) + _1

-- (ii) collatz(n) := h(n, d(n)), where d decides 2 ∣ n (Theorem 8.1.9).
def collatz (n : myN) : myN := collatz_h n (is_decidable_divides _2 n)


/- Remark 8.2.2: with-abstraction.  In Lean, `match` on a term that is not a
   variable plays the role of with-abstraction: it generalizes the term
   `is_decidable_divides _2 n` to a variable and then proceeds by pattern
   matching, so that the auxiliary function h no longer has to be named:

     collatz(n) with [d(n) / inl(k, p)] := k
     collatz(n) with [d(n) / inr(f)]    := 3n + 1                               -/
def collatz' (n : myN) : myN :=
  match is_decidable_divides _2 n with
  | Sum.inl ⟨k, _⟩ => k
  | Sum.inr _ => (_3 * n) + _1

-- Both definitions agree judgmentally.
def collatz'_eq_collatz (n : myN) : (collatz' n) ≡ (collatz n) := MyEq.refl _


/- The Collatz function satisfies its specification.  The proofs again proceed by
   case analysis on an arbitrary decision d, which is then instantiated. -/

def collatz_h_even (n : myN) :
    (d : is_decidable (divides _2 n)) → divides _2 n → (_2 * collatz_h n d) ≡ n
  | Sum.inl ⟨_, p⟩, _ => p
  | Sum.inr f, h => Empty.elim (f h)

def collatz_h_odd (n : myN) :
    (d : is_decidable (divides _2 n)) → myNegType (divides _2 n) →
      (collatz_h n d) ≡ ((_3 * n) + _1)
  | Sum.inl p, f => Empty.elim (f p)
  | Sum.inr _, _ => MyEq.refl _

-- If n is even, then 2 · collatz(n) = n.
def collatz_even (n : myN) (h : divides _2 n) : (_2 * collatz n) ≡ n :=
  collatz_h_even n (is_decidable_divides _2 n) h

-- If n is odd, then collatz(n) = 3n + 1.
def collatz_odd (n : myN) (h : myNegType (divides _2 n)) : (collatz n) ≡ ((_3 * n) + _1) :=
  collatz_h_odd n (is_decidable_divides _2 n) h

-- Since the decision procedure computes, so does the Collatz function.
example : (collatz _6) ≡ _3 := MyEq.refl _
example : (collatz _3) ≡ _10 := MyEq.refl _
example : (collatz (ofNatN 7)) ≡ (ofNatN 22) := MyEq.refl _


/- ###################################################################### -/
/-  Proposition 8.2.3                                                      -/
/- ###################################################################### -/

/- If A is decidable and B is decidable under the assumption A, then A × B and
   A → B are decidable. -/

def is_decidable_prod' {A B : Type} (dA : is_decidable A) (dB : A → is_decidable B) :
    is_decidable (myProd A B) :=
  match dA with
  | Sum.inr f => Sum.inr (f ∘ proj1)
  | Sum.inl a =>
      -- with-abstraction on dB(a)
      match dB a with
      | Sum.inl b => Sum.inl (myProd.mk a b)
      | Sum.inr g => Sum.inr (g ∘ proj2)

def is_decidable_fun' {A B : Type} (dA : is_decidable A) (dB : A → is_decidable B) :
    is_decidable (A → B) :=
  match dA with
  | Sum.inr f => Sum.inl (fun a => Empty.elim (f a))
  | Sum.inl a =>
      -- with-abstraction on dB(a)
      match dB a with
      | Sum.inl b => Sum.inl (fun _ => b)
      | Sum.inr g => Sum.inr (fun h => g (h a))


/- ###################################################################### -/
/-  Proposition 8.2.4 and Corollary 8.2.5                                  -/
/- ###################################################################### -/

/- Proposition 8.2.4.  Let P be a decidable family over ℕ and m : ℕ such that
   Π (x : ℕ), (m ≤ x) → P(x) is decidable.  Then Π (x : ℕ), P(x) is decidable.

   The proof is by induction on m, for all decidable families P at once (in Lean
   the family P is simply an argument of the recursive function, which plays the
   role of the universe U of the book). -/
def is_decidable_pi_of_bound : (m : myN) → (P : myN → Type) → is_decidable_family P →
    is_decidable ((x : myN) → leq m x → P x) → is_decidable ((x : myN) → P x)
  | myN.zero, _, _, h =>
      is_decidable_of_iff (myProd.mk (fun f x => f x ()) (fun g x _ => g x)) h
  | myN.succ m, P, d, h =>
      match d myN.zero with
      | Sum.inr np => Sum.inr (fun f => np (f myN.zero))
      | Sum.inl p0 =>
          -- the family P'(x) := P(x + 1)
          let h' : is_decidable ((x : myN) → leq m x → P (myN.succ x)) :=
            is_decidable_of_iff
              (myProd.mk
                (fun f x q => f (myN.succ x) q)
                (fun g y q =>
                  match y, q with
                  | myN.zero, q => Empty.elim q
                  | myN.succ y, q => g y q))
              h
          match is_decidable_pi_of_bound m (fun x => P (myN.succ x)) (fun x => d (myN.succ x)) h' with
          | Sum.inl f =>
              Sum.inl (fun x =>
                match x with
                | myN.zero => p0
                | myN.succ x => f x)
          | Sum.inr nf => Sum.inr (fun f => nf (fun x => f (myN.succ x)))

-- m + 1 ≤ m is impossible
def not_leq_succ_self (m : myN) : myNegType (leq (myN.succ m) m) :=
  fun h => less_than_irrefl m (less_than_of_leq m m h)

/- Corollary 8.2.5.  Let P and Q be decidable families over ℕ, and let m be an upper
   bound for P.  Then Π (x : ℕ), P(x) → Q(x) is decidable. -/
def is_decidable_pi_implication (P Q : myN → Type)
    (dP : is_decidable_family P) (dQ : is_decidable_family Q)
    (m : myN) (ub : (x : myN) → P x → leq x m) :
    is_decidable ((x : myN) → P x → Q x) :=
  is_decidable_pi_of_bound (myN.succ m) (fun x => P x → Q x)
    (fun x => is_decidable_fun (dP x) (dQ x))
    -- beyond the upper bound m, the implication P(x) → Q(x) holds vacuously
    (Sum.inl (fun x h p =>
      Empty.elim (not_leq_succ_self m (leq_trans (myN.succ m) x m h (ub x p)))))

end chapter8
