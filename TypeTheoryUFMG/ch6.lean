import TypeTheoryUFMG.ch5

-- Chapter 6

namespace ex6_10

variable (S:Prop) (P1 P2:S -> Prop)

theorem aux (S:Prop) (P1 P2 : S -> Prop) (x:S) : P1 x -> P2 x -> P2 x := by
  exact λ _ : P1 x => λ b : P2 x => b


def R (S:Prop) (P1 P2:S -> Prop) (x:S):= ((Q:S -> Prop) -> ((y:S) -> P1 y -> P2 y -> Q y) -> Q x)

theorem ex6_10a :
  (x:S) -> P1 x -> P2 x -> R S P1 P2 x := by

  intro x a b Q z
  exact z x a b

theorem ex6_10b:
  (x:S) -> R S P1 P2 x -> P1 x := by

  intro x z
  have p := ex5_8 S P1 P2 -- ex5_8 shows that p -> q -> p
  exact z P1 p

theorem ex6_10c:
  (x:S) -> R S P1 P2 x -> P2 x := by

  intro x z
  have p := aux S P1 P2 -- aux shows that p -> q -> q
  exact z P2 p

end ex6_10
