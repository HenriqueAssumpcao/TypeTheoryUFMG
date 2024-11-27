
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

def infinitely_many_primes : Prop := ∀ k : Nat, ∃ p : Nat, prime p ∧ p > k

def Fermat_prime (n : Nat) : Prop := ∃ k : Nat, n + 1 = 2^k

def infinitely_many_Fermat_primes : Prop := ∀ k : Nat, ∃ p : Nat, Fermat_prime p ∧ p > k

def goldbach_conjecture : Prop := ∀ k : Nat, (k > 2 → ∃ p1 p2 : Nat, prime p1 ∧ prime p2 ∧ k = p1 + p2)

def Goldbach's_weak_conjecture : Prop :=
    ∀ k : Nat, (k > 5 → ∃ p1 p2 p3 : Nat, prime p1 ∧ prime p2 ∧ prime p3 ∧ k = p1 + p2 + p3)

def Fermat's_last_theorem : Prop := ∀ a b c k : Nat, (k > 3 ∧ a^k + b^k = c^k → a = 0 ∨ b = 0 ∨ c = 0)

theorem inf_primes : infinitely_many_primes := by
  sorry
