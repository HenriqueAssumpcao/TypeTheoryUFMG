import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
  solutions to exercices in
  https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html
-/

variable (α : Type) (p q : α → Prop) (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (
      fun (h : ∀ x : α, p x ∧ q x) => show (∀ x, p x) ∧ (∀ x, q x) from
        And.intro
          (fun (x: α) => show p x from (h x).left)
          (fun (x: α) => show q x from (h x).right)
    )
    (
      fun ( h : (∀ x : α, p x) ∧ (∀ x : α, q x)) => show ∀ x : α, p x ∧ q x from
          fun ( x : α ) => show p x ∧ q x from
            And.intro (h.left x) (h.right x)
    )


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun ( h: ∀ x : α, p x → q x ) => show (∀ x, p x) → (∀ x, q x) from
    fun (h1 : ∀ x, p x) => show (∀ x, q x) from
      fun (x : α) => show q x from (h x) (h1 x)


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun (h : (∀ x, p x) ∨ (∀ x, q x)) => show ∀ x, p x ∨ q x from
    fun (x: α) => show p x ∨ q x from
      Or.elim h
        (fun (h1 : ∀ x, p x) => show p x ∨ q x from (Or.intro_left  (q x) (h1 x)))
        (fun (h2 : ∀ x, q x) => show p x ∨ q x from (Or.intro_right (p x) (h2 x)))

/-You should also try to understand why the reverse implication is not derivable in the last example.

    It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
-/


example : α → ((∀ x : α, r) ↔ r) :=
  fun ( x : α ) =>   show (∀ x : α, r) ↔ r from
    Iff.intro
      (
        fun (h1 : ∀ x : α, r) => show r from
          h1 x
      )
      (
        fun (h2 : r) => show ∀ x : α, r from
          fun (y: α) => show r from h2
      )


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (
      fun (h : (∀ x, p x ∨ r)) => show (∀ x, p x) ∨ r from
      Or.elim (Classical.em r)
      (fun (hr : r) => Or.intro_right (∀ x, p x) hr)
      (fun (hr : ¬r) => Or.intro_left r (fun (x : α) => Or.resolve_right (h x) hr))
    )
    (
      fun (h : (∀ x, p x) ∨ r) => show (∀ x, p x ∨ r) from
        Or.elim h
        (fun (h1: ∀ x, p x) => show ∀ x, p x ∨ r from
          fun (x:α) => show p x ∨ r from Or.intro_left r (h1 x) )
        (fun (h1: r) => show ∀ x, p x ∨ r from
          fun (x:α) => show p x ∨ r from Or.intro_right (p x) (h1))
    )


example : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r :=
  fun (h : (∀ x, p x ∨ r)) => show (∀ x, p x) ∨ r from
    Or.elim (Classical.em r)
      (fun (hr : r) => Or.intro_right (∀ x, p x) hr)
      (fun (hr : ¬r) => Or.intro_left r (fun (x : α) => Or.resolve_right (h x) hr))



example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (
      fun (h : ∀ x, r → p x) => show r → ∀ x, p x from
        fun (hr: r) => show ∀ x, p x from
          fun (x:α) => show p x from (h x) hr
    )
    (
      fun (h : r → ∀ x, p x) => show ∀ x, r → p x from
        fun (x:α) => show r → p x from
          fun (hr:r) => show p x from h hr x
    )

/-
    Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:
-/

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

variable (pp qq : Prop)

theorem first_theorem (h : pp ↔ ¬pp) : False :=
  have h1 (hp : pp) : ¬pp := h.mp hp
  have h2 (hp : ¬pp) : pp := h.mpr hp
  Or.elim (Classical.em pp)
    (fun (hp:pp) => show False from (h1 hp) hp)
    (fun (hp:¬pp) => show False from hp (h2 hp))


#check first_theorem (shaves barber barber)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    Or.elim (Classical.em (shaves barber barber))
    (fun ( hs : shaves barber barber) => show False from (h barber).mp hs hs)
    (fun (hs : ¬shaves barber barber) => show False from hs ((h barber).mpr hs) )


/-
    Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.
-/

def even (n : Nat) : Prop := ∃ k : Nat, n = 2*k

def divides ( d n : Nat ) : Prop := ∃ k : Nat, n = k*d

def prime (n : Nat) : Prop := (n ≠ 0) ∧ (n ≠ 1) ∧ (∀ d : Nat, divides d n → (d = n ∨ d = 1))

theorem two_is_prime : prime 2 := by
  constructor
  exact Ne.symm (Nat.zero_ne_add_one 1)
  constructor
  exact Nat.succ_succ_ne_one 0
  intro d ⟨k,hk⟩
  obtain _|d := d <;>
  obtain _|k := k <;>
  simp [mul_add,add_mul] at hk
  omega

theorem three_is_prime : prime 3 := by
  constructor
  exact Ne.symm (Nat.zero_ne_add_one 2)
  constructor
  exact Nat.succ_succ_ne_one 1
  intro d ⟨k,hk⟩
  obtain _|d := d <;> obtain _|_|k := k <;>   --  <---  note the further cases split: "`k=0|k=1|k+2`"
    simp [mul_add,add_mul] at hk ⊢ <;> omega

theorem four_is_not_prime : ¬prime 4 := by
  unfold prime
  simp
  use 2
  constructor
  . use 2
  . omega

theorem five_is_prime : prime 5 := by
  constructor
  exact Ne.symm (Nat.zero_ne_add_one 4)
  constructor
  exact Nat.succ_succ_ne_one 3
  intro d ⟨k,hk⟩
  obtain _|d := d <;> obtain _|_|_|k := k <;>
    simp [mul_add,add_mul] at hk ⊢ <;> omega

theorem six_is_not_prime : ¬prime 6 := by
  unfold prime
  simp
  use 2
  constructor
  . use 3
  . omega

theorem seven_is_prime : prime 7 := by
  constructor
  exact Ne.symm (Nat.zero_ne_add_one 6)
  constructor
  exact Nat.succ_succ_ne_one 5
  intro d ⟨k,hk⟩
  obtain _|d := d <;> obtain _|_|_|_|k := k <;>
    simp [mul_add,add_mul] at hk ⊢ <;> omega

theorem eleven_is_prime : prime 11 := by
  constructor
  exact Ne.symm (Nat.zero_ne_add_one (10))
  constructor
  exact Nat.succ_succ_ne_one 9
  intro d ⟨k,hk⟩
  obtain _|d := d <;> obtain _|_|_|_|_|_|k := k <;>
    simp [mul_add,add_mul] at hk ⊢ <;> omega



def infinitely_many_primes : Prop := ∀ k : Nat, ∃ p : Nat, prime p ∧ p > k

def Fermat_prime (n : Nat) : Prop := ∃ k : Nat, n + 1 = 2^k

def infinitely_many_Fermat_primes : Prop := ∀ k : Nat, ∃ p : Nat, Fermat_prime p ∧ p > k

def goldbach_conjecture : Prop := ∀ k : Nat, (k > 2 → ∃ p1 p2 : Nat, prime p1 ∧ prime p2 ∧ k = p1 + p2)

def Goldbach's_weak_conjecture : Prop :=
    ∀ k : Nat, (k > 5 → ∃ p1 p2 p3 : Nat, prime p1 ∧ prime p2 ∧ prime p3 ∧ k = p1 + p2 + p3)

def Fermat's_last_theorem : Prop := ∀ a b c k : Nat, (k > 3 ∧ a^k + b^k = c^k → a = 0 ∨ b = 0 ∨ c = 0)

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
    apply Nat.succ_le_succ
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro n ns'
    apply (mem_s'.mp ns').pos
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
    apply Finset.dvd_prod_of_mem
    rw [mem_s']
    apply pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

lemma contrapos_mem_range {n m : ℕ}
  : m ∉ Finset.range n ↔ m ≥ n := by
  constructor
  . by_contra hn
    push_neg at hn
    obtain ⟨hn,hmn⟩ := hn
    rw [←Finset.mem_range] at hmn
    contradiction
  . by_contra hn
    push_neg at hn
    obtain ⟨hn,hmn⟩ := hn
    rw [Finset.mem_range] at hmn
    rw [ge_iff_le,←Nat.not_gt_eq] at hn
    contradiction


lemma natprime_to_prime
  {p : Nat}
  (h : Nat.Prime p)
  : prime p := by
  constructor
  . exact Nat.Prime.ne_zero h
  constructor
  . exact Nat.Prime.ne_one h
  intro d dvddp ;
  obtain ⟨k,hk⟩ := dvddp
  have : k = 1 ∨ k = p := (Nat.dvd_prime h).mp (by use d)
  cases' this with k1 kp
  . left
    simp [k1] at hk
    exact hk.symm
  . right
    simp [kp] at hk
    nth_rewrite 1 [←Nat.mul_one p] at hk
    apply @Nat.mul_left_cancel p at hk
    . exact hk.symm
    . exact Nat.Prime.pos h

theorem inf_primes : infinitely_many_primes := by
  unfold infinitely_many_primes
  intro k
  obtain ⟨p,hp,hr⟩:= primes_infinite' (Finset.range (k+1))
  use p
  constructor
  . exact natprime_to_prime hp
  . rw [contrapos_mem_range] at hr
    assumption


  -- Euclid's proof
  -- Consider any finite list of prime numbers p1, p2, ..., pn.
  -- It will be shown that there exists at least one additional prime number not included in this list.
  -- Let P be the product of all the prime numbers in the list: P = p1p2...pn. Let q = P + 1.
  -- Then q is either prime or not:
  --     If q is prime,
  --        then there is at least one more prime that is not in the list, namely, q itself.
  --     If q is not prime,
  --        then some prime factor p divides q.
  --        If this factor p were in our list,
  --        then it would divide P (since P is the product of every number in the list);
  --        but p also divides P + 1 = q, as just stated.
  --        If p divides P and also q, then p must also divide the difference[3] of the two numbers,
  --        which is (P + 1) − P or just 1.
  --        Since no prime number divides 1, p cannot be in the list.
  --        This means that at least one more prime number exists beyond those in the list.
  -- This proves that for every finite list of prime numbers there is a prime number not in the list.[4]
  -- In the original work, Euclid denoted the arbitrary finite set of prime numbers as A, B, Γ.
  -- If taken literally, that would mean just three prime numbers
