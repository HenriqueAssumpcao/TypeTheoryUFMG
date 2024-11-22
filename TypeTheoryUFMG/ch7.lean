-- Chapter 7

namespace c7ex1

variable (A B :Prop)

theorem sol_a :
  B -> (A -> B) := by

  exact λ (b: B) => λ (_: A) => b

theorem sol_b :
  ¬ A -> A -> B := by

  exact λ (a: ¬ A) => λ (b: A) => False.elim (a b)

theorem sol_c :
  (A -> ¬ B) -> ((A -> B) -> ¬ A) := by

  sorry

theorem sol_d:
  ¬(A -> B) -> ¬ B := by

  sorry

end c7ex1


namespace c7ex8

variable (A B :Prop)

theorem sol_a :
  (A ∨ B) -> (B ∨ A) := by

  intro P
  let f1 : (A -> B ∨ A) := λ (a:A) => Or.inr a
  let f2 : (B -> B ∨ A) := λ (b:B) => Or.inl b
  exact Or.elim P f1 f2

theorem sol_b:
  ¬ (A ∨ B) -> (¬ A ∧ ¬ B) := by

  sorry

theorem sol_c:
  (¬ A ∧ ¬ B) -> ¬(A ∨ B) := by

  sorry

end c7ex8

namespace c7ex9

variable (S:Prop) (P Q R : S -> Prop)

theorem sol_a :
  (x:S) -> (¬ P x -> ((P x) -> (Q x) ∧ (R x))) := by

  intro x a b
  let p := a b
  let c : (Q x) ∧ (R x) := False.elim p
  exact c

  -- Same as λ (a:¬ P x) => λ (b: P x) => False.elim (a b)

theorem sol_b :
  ((x:S) -> P x) -> ((y:S) -> (P y ∨ Q y)) := by

  intro A
  exact λ (a:S) => Or.inl (A a)

end c7ex9



namespace c7ex10

variable (S:Prop) (P Q R : S -> Prop)

theorem sol :
  ((x:S) -> (P x -> Q x)) -> ((y:S) -> (P y -> R y)) -> ((z:S) -> (P z -> (Q z ∧ R z))) := by

  intro A B z a
  let c : Q z := A z a
  let d : R z := B z a
  exact And.intro c d

  -- Same as λ (z:S) => λ (a: P z) => And.intro (A z a) (B z a)

end c7ex10
