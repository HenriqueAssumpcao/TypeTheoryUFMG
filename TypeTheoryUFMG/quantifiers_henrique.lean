
-- Solutions for the exercises in https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html

namespace ex1

variable (S:Prop) (P Q: S -> Prop)

theorem sol1 :
  (∀x:S,P x ∧ Q x) ↔ (∀x:S,P x) ∧ (∀x:S, Q x) := by
  apply Iff.intro 
  . intro h1
    let f1 := λ (x:S) => (h1 x).left 
    let f2 := λ (x:S) => (h1 x).right 
    exact ⟨f1,f2⟩ 
  . intro h2
    let px := h2.left 
    let qx := h2.right 
    exact λ (x:S) => ⟨px x, qx x⟩ 

theorem sol2 :
  (∀ x:S,P x -> Q x) -> (∀ x:S,P x) -> (∀ x:S,Q x) := by

  intro fxpq fxp x 
  exact fxpq x (fxp x)

theorem sol3 :
  (∀x:S, P x) ∨ (∀x:S, Q x) -> (∀ x:S, P x ∨ Q x) := by

  intro poq x
  cases poq with
  | inl fpx => exact Or.inl (fpx x) 
  | inr fqx => exact Or.inr (fqx x)

namespace ex1 

namespace ex2 

variable (S:Type) (R:Prop) (P Q:S->Prop)


theorem sol1 : 
  S -> ((∀ x:S, R) ↔ R) := by

  intro x
  apply Iff.intro 
  . intro h1
    exact h1 x
  . intro h2
    exact λ (x:S) => h2



theorem sol2 :
  (∀ x:S,P x ∨ R) ↔ (∀ x:S, P x) ∨ R := by

  apply Iff.intro 
  . intro h1
    let f := λ (nr:¬R) => λ (x:S) => (h1 x).resolve_right nr 
    let ronr := Classical.em R 
    cases ronr with
    | inl r => exact Or.inr r 
    | inr nr => exact Or.inl (f nr)
    
  . intro h2
    cases h2 with
    | inl fx => exact λ (x:S) => Or.inl (fx x)
    | inr r => exact λ (x:S) => Or.inr (r)


theorem sol3 :
  (∀ x:S, R -> P x) ↔ (R -> (∀ x:S, P x)) := by

  apply Iff.intro
  . intro h1 r
    exact λ (x:S) => h1 x r
  . intro h2 x r 
    exact h2 r x


end ex2

namespace ex3 

variable (men:Type) (barber:men) (shaves:men -> men -> Prop)

theorem barber_paradox :
  (∀ x:men, shaves barber x ↔ ¬ shaves x x) -> False := by
  intro h
  let abs := h barber
  let p := Classical.em (shaves barber barber)
  cases p with 
  | inl t => exact (abs.mp t) t
  | inr f => exact f (abs.mpr f) 

end ex3


namespace ex4


def even (n:Nat) : Prop := ∃ x:Nat, n = 2*x 

def prime (n:Nat) : Prop := (n ≠ 0) ∧ (n ≠ 1) ∧ (∀x:Nat, ∃k:Nat, n = k*x -> (x = 1 ∨ x = n))

def infinitely_many_primes: Prop := ∀n:Nat,∃p:Nat,prime p ∧ p > n

def fermat_prime (n:Nat) : Prop := ∃k:Nat, n = Nat.pow 2 (Nat.pow 2 k) + 1

def infinitely_many_fermat_primes : Prop := ∀n:Nat,∃q:Nat,fermat_prime q ∧ q > n 

def goldbach_conjecture : Prop := ∀n:Nat, even n ∧ (n > 2) -> ∃p:Nat,∃q:Nat, prime p ∧ prime q ∧ n = p + q

def goldback_weak_conjecture : Prop := ∀n:Nat, (¬ even n) ∧ (n > 5) -> ∃p:Nat,∃q:Nat,∃z:Nat, prime p ∧ prime q ∧ prime z ∧ n = p + q + z

def fermat_last_theorem : Prop := ∀n:Nat, n > 2 -> ¬∃a:Nat,¬∃b:Nat,¬∃c:Nat, Nat.pow a n + Nat.pow b n = Nat.pow c n

end ex4
