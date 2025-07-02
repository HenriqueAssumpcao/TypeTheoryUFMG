-- solutions to exercices in https://leanprover.github.io/theorem_proving_in_lean4/tactics.html



variable (p q r : Prop)


/-
This example proves the equivalence of the conjunction of `p` and `q` with the conjunction of `q` and `p`.
The proof is done using the `Iff.intro` tactic, which requires two arguments: a proof of `p ∧ q` implying `q ∧ p`, and a proof of `q ∧ p` implying `p ∧ q`.

The first argument is a lambda function that takes a proof `h : p ∧ q` and returns a proof of `q ∧ p`. Inside the lambda function, we use the `show` tactic to explicitly state that we want to prove `q ∧ p`. We then use the `And.intro` tactic to construct a proof of `q ∧ p` by swapping the left and right components of `h`.

The second argument is a lambda function that takes a proof `h : q ∧ p` and returns a proof of `p ∧ q`. Inside the lambda function, we use the `show` tactic to explicitly state that we want to prove `p ∧ q`. We then use the `And.intro` tactic to construct a proof of `p ∧ q` by swapping the left and right components of `h`.
-/

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun h : q ∧ p => And.intro h.right h.left)


example : p ∧ q ↔ q ∧ p  :=
  Iff.intro
    (λ h : p ∧ q => ⟨h.right, h.left⟩)
    (λ h : q ∧ p => ⟨h.right, h.left⟩)
    -- the same type of lambda function


example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  case mp => intro h
             apply And.intro h.right h.left
  case mpr => intro h
              apply And.intro h.right h.left


example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro h
    apply And.intro h.right h.left
  · intro h
    apply And.intro h.right h.left


theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (
      fun h : p ∨ q => show q ∨ p from
        Or.elim h (fun h : p => show q ∨ p from Or.intro_right q h ) (fun h : q => show q ∨ p from Or.intro_left p h)
    )

    (
      fun h : q ∨ p => show p ∨ q from
        Or.elim h  (fun h : q => show p ∨ q from Or.intro_right p h) (fun h : p => show p ∨ q from Or.intro_left q h )
    )


example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  · intro h
    apply Or.elim h
    · intro h1
      apply Or.inr h1
    · intro h2
      apply Or.inl h2
  · intro h
    apply Or.elim h
    · apply Or.inr
    · apply Or.inl

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (
      λ h : p ∨ q =>
        Or.elim h (λ h : p => Or.intro_right q h ) ( λ h : q => Or.intro_left p h)
    )

    (
      λ h : q ∨ p =>
        Or.elim h  (λ  h : q => Or.intro_right p h) (λ  h : p => Or.intro_left q h )
    )



example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (
      fun h : p ∨ q =>
      Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq)
    )
    (
      fun h : q ∨ p =>
      Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp)
    )


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (
      fun h : (p ∧ q) ∧ r => show p ∧ (q ∧ r) from
        And.intro
          (And.left (And.left h))
          (And.intro (And.right (And.left h)) (And.right h))
    )

    (
      fun h : p ∧ (q ∧ r) => show (p ∧ q) ∧ r from
        And.intro
          (And.intro (And.left h) (And.left (And.right h)))
          (And.right (And.right h))
    )

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  · intro h
    apply And.intro
    exact h.left.left
    apply And.intro
    exact h.left.right
    exact h.right
  · intro h
    apply And.intro
    apply And.intro
    exact h.left
    exact h.right.left
    exact h.right.right


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (
      fun h : (p ∨ q) ∨ r => show p ∨ (q ∨ r) from
        Or.elim h
          (
            fun h1 : p ∨ q => show p ∨ (q ∨ r) from
            Or.elim h1
              (fun h3 : p => show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) h3)
              (fun h4 : q => show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r h4))
          )

          (fun h2 : r =>  show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q h2))
    )
    (
      fun h : p ∨ (q ∨ r) => show (p ∨ q) ∨ r from
        Or.elim h
        (
          fun h1 : p => show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q h1)
        )
        (
          fun h2 : q ∨ r => show (p ∨ q) ∨ r from
            Or.elim h2
              (
                fun h3 : q => show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p h3)
              )
              (
                fun h4 : r => show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) h4
              )
      )
    )


example : (p ∨ q) ∨ r ↔  p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    intro h1
    apply Or.elim h1
    · apply Or.inl
    · intro  h2
      have h3 : q ∨ r := Or.intro_left r h2
      apply Or.intro_right p h3
    · intro h2
      have h3 : q ∨ r := Or.intro_right q h2
      apply Or.intro_right p h3
  · intro h
    apply Or.elim h
    · intro h1
      have h2 : p ∨ q := Or.intro_left q h1
      apply Or.inl h2
    · intro h1
      apply Or.elim h1
      . intro h2
        have h3 : p ∨ q := Or.intro_right p h2
        apply Or.inl h3
      · apply Or.inr









-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (
    fun h : p ∧ (q ∨ r) => show (p ∧ q) ∨ (p ∧ r) from
      Or.elim h.right
        (fun hq : q => show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro h.left hq))
        (fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro h.left hr))
  )

  (
    fun h : (p ∧ q) ∨ (p ∧ r) => show p ∧ (q ∨ r) from
      Or.elim h
      (fun hpq : p ∧ q => And.intro hpq.left (Or.intro_left r hpq.right))
      (fun hpr : p ∧ r => And.intro hpr.left (Or.intro_right q hpr.right))
  )


example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
apply Iff.intro
· intro h
  apply Or.elim h.right
  · intro h1
    have h2 : p ∧ q := And.intro h.left h1
    apply Or.intro_left (p ∧ r) h2
  · intro h1
    have h2 : p ∧ r := And.intro h.left h1
    apply Or.intro_right (p ∧ q) h2
· intro h
  apply Or.elim h
  · intro h1
    apply And.intro h1.left (Or.intro_left r h1.right)
  · intro h1
    apply And.intro h1.left (Or.intro_right q h1.right)


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (
    fun h : p ∨ (q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from
      Or.elim h
        (
          fun hp : p => show (p ∨ q) ∧ (p ∨ r) from
          And.intro (Or.intro_left q hp) (Or.intro_left r hp)
        )
        (
          fun hqr : q ∧ r => show (p ∨ q) ∧ (p ∨ r) from
          And.intro (Or.intro_right p hqr.left) (Or.intro_right p hqr.right)
        )
  )

  (
    fun hpqpr : (p ∨ q) ∧ (p ∨ r) => show p ∨ (q ∧ r) from
      Or.elim hpqpr.left
      (fun hp : p => show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
      (
        fun hq : q => show p ∨ (q ∧ r) from
        Or.elim hpqpr.right
          (fun hp1 : p => show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp1)
          (fun hr : r => show p ∨ (q ∧ r) from Or.intro_right p (And.intro hq hr))
    )
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (
      fun h : (p → (q → r)) => show (p ∧ q → r) from
        fun hpq : p ∧ q => show r from
        (h hpq.left) hpq.right
    )
    (
      fun h : (p ∧ q) → r => show p → (q → r) from
        fun hp : p => show q → r from
          fun hq : q => show r from
            h (And.intro hp hq)
    )

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  · intro h
    intro ph
    apply h ph.left ph.right
  · intro h
    intro hp hq
    have hpq : p ∧ q := And.intro hp  hq
    apply h hpq



example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (
    fun h : (p ∨ q) → r => show (p → r) ∧ (q → r) from
    And.intro
      (fun hp : p => show r from h (Or.intro_left q hp))
      (fun hq : q => show r from h (Or.intro_right p hq))
  )
  (
    fun hh : (p → r) ∧ (q → r) => show (p ∨ q) → r from
      fun hpq : p ∨ q => show r from
        Or.elim hpq
          (fun hp : p => show r from hh.left hp)
          (fun hq : q => show r from hh.right hq)
  )


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (
    fun h : ¬(p ∨ q) => show ¬p ∧ ¬q from
    And.intro
      (fun hp : p => show False from h (Or.intro_left q hp)  )
      (fun hq : q => show False from h (Or.intro_right p hq))
  )
  (
    fun h : ¬p ∧ ¬q => show ¬(p ∨ q) from
      (fun hpq : p ∨ q => show False from
        Or.elim hpq (fun hp : p => show False from h.left hp) (fun hq : q => show False from h.right hq))
  )


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hpq : ¬p ∨ ¬q => show ¬(p ∧ q) from
    Or.elim hpq
      (fun hp : ¬p => show ¬(p ∧ q) from
        fun hpq1 : p ∧ q => show False from hp hpq1.left)
      (fun hq : ¬q => show ¬(p ∧ q) from
        fun hpq1 : p ∧ q => show False from hq hpq1.right)


example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => show False from
    h.right h.left


example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q => show ¬(p → q) from
    fun hpq : (p → q) => show False from
      h.right (hpq h.left)

example : ¬p → (p → q) :=
  fun h : ¬p => show p → q from
    fun hp : p => show q from
       False.elim (h hp)


example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q => show p → q from
    Or.elim h
    (fun hnp : ¬p => show p → q from
      fun hp : p => show q from False.elim (hnp hp))
    (fun hq : q => show p -> q from
      fun _ : p => show q from hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (
      fun hpf : p ∨ False => show p from
        Or.elim hpf
          (fun hp : p => show p from hp)
          (fun f : False => show p from False.elim f )
    )
    (
      fun hp : p => show p ∨ False from Or.intro_left False hp
    )


example : p ∧ False ↔ False :=
  Iff.intro
    (
      fun h : p ∧ False => h.right
    )
    (
      fun f : False => False.elim f
    )

example : (p → q) → (¬q → ¬p) :=
  fun h : p → q => show ¬q → ¬p from
    fun hq : ¬q => show ¬p from
      fun hp : p => show False from
       hq  (h hp)
