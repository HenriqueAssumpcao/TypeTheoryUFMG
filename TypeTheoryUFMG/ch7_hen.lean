-- code by @HenriqueAssumpcao

-- Chapter 7

-- Section examples

namespace c7sec3

variable (A B :Prop)

theorem sol_lambdaC :
  ((C:Prop) -> ((A -> C) -> (B -> C) -> C)) -> (A -> False) -> B := by

  intro x y
  let xb := x B
  let f : (A -> B) := λ (u:A) => False.elim (y u)
  let g : (B -> B) := λ (v : B) => v
  exact xb f g

theorem sol_logic :
  (A ∨ B) -> (¬ A -> B) := by

  intro aorb na
  exact Or.resolve_left aorb na

end c7sec3

namespace c7sec4

theorem sol :
  ((α:Prop) -> ((C:Prop) -> (α -> C) -> (¬α -> C) -> C)) -> ((β:Prop) -> ¬¬β -> β) := by

  intro i b x
  let f : (b -> b) := id
  let g : (¬ b -> b) := λ (z:¬ b) => False.elim (x z)
  exact i b b f g

end c7sec4

namespace c7sec6

variable (S:Prop) (P:S -> Prop)


theorem sol :
  ¬(∃ x:S, P x) -> (∀ x:S, ¬ (P x)) := by

  intro nex x px

  let ex := Exists.intro x px
  exact nex ex

end c7sec6


-- Exercises

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

  intro ainb aib a
  let P := And.imp ainb aib (And.intro a a)
  let b := And.left P
  let nb := And.right P
  exact b nb

theorem sol_d:
  ¬(A -> B) -> ¬ B := by

  intro naib b
  let aib := sol_a A B b
  exact naib aib

end c7ex1


namespace c7ex8

variable (A B :Prop)

theorem sol_a :
  (A ∨ B) -> (B ∨ A) := by

  intro P
  let f1 : (A -> B ∨ A) := λ (a:A) => Or.inr a
  let f2 : (B -> B ∨ A) := λ (b:B) => Or.inl b
  exact Or.elim P f1 f2

theorem DN : ∀ A : Prop, ¬¬A → A :=
  λ A nna => Or.elim (Classical.em (A))
    (λ a => a)
    (λ na => absurd na nna)

theorem sol_b: ¬(A ∨ B) -> (¬ A ∧ ¬ B) :=
  λ z => And.intro
    (DN (¬A) λ nna => z (Or.inl (DN A nna)))
    (DN (¬B) λ nnb => z (Or.inr (DN B nnb)))

theorem sol_b': ¬(A ∨ B) -> (¬ A ∧ ¬ B) := by
  intro z
  constructor
  . apply DN
    intro nna
    have a : A := DN A nna
    have aORb : A ∨ B := Or.inl a
    exact z aORb
  . apply DN
    intro nnb
    have b : B := DN B nnb
    have aORb : A ∨ B := Or.inr b
    exact z aORb

theorem sol_c:
  (¬ A ∧ ¬ B) -> ¬(A∨B) := by

  intro P Q
  let na := And.left P
  let nb := And.right P
  let b := Or.resolve_left Q na
  exact nb b

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


namespace c7ex13

variable (S:Prop) (P Q:S -> Prop)

theorem sol :
  (∃ x:S, P x) -> (∀ y:S,(P y -> Q y)) -> (∃ z : S, Q z) := by

  intro exx fay

  let x := exx.choose
  let px := exx.choose_spec
  let f := fay x
  exact Exists.intro x (f px)


end c7ex13
