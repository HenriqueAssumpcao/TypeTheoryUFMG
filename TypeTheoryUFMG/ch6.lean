import TypeTheoryUFMG.ch5

-- Chapter 6


namespace c6ex7

variable (S:Prop) (Q:S -> S -> Prop)

def M1 (S:Prop) := λ (x y :S) => (R:S -> S -> Prop) -> (((z:S) -> R z z)-> R x y)

def M2 (S:Prop) (Q:S -> S -> Prop) := λ (x y : S) => (R:S -> S -> Prop) -> ((u v : S) -> (Q u v -> R u v)) -> R x y

theorem sol_a :
  (a : S) -> (M1 S a a) := by

  intro a R b
  exact b a
  -- Same as: exact λ (R:S -> S -> Prop) => λ (b : (z:S) -> R z z) => b a


theorem sol_b :
  (a b : S) -> ((Q a b) -> (M2 S Q a b)) := by

  intro a b c R f
  exact f a b c
  -- Same as: exact λ (R: S -> S -> Prop) => λ (f : ((u v : S) -> ((Q u v) -> R u v))) => f a b c

end c6ex7


namespace c6ex9
variable (S:Prop) (P:S -> Prop) (f:S -> S)

def M (S:Prop) (f: S -> S) := λ (x:S) => (Q:S -> Prop) -> (((z:S) -> (Q z -> Q (f z))) -> Q x)

theorem sol :
  (a:S) -> (M S f a -> M S f (f a)) := by

  intro a b Q c
  exact (c a) (b Q c)
  -- Same as: exact λ (b: M S f a) => λ (Q:S -> Prop) => λ (c: (z:S) -> (Q z -> Q (f z))) => (c a) (b Q c)

end c6ex9


namespace c6ex10

variable (S:Prop) (P1 P2:S -> Prop)

theorem aux (S:Prop) (P1 P2 : S -> Prop) (x:S) : P1 x -> P2 x -> P2 x := by
  exact λ _ : P1 x => λ b : P2 x => b


def R (S:Prop) (P1 P2:S -> Prop):= λ (x:S) => ((Q:S -> Prop) -> ((y:S) -> P1 y -> P2 y -> Q y) -> Q x)

theorem sol_a :
  (x:S) -> P1 x -> P2 x -> R S P1 P2 x := by

  intro x a b Q z
  exact z x a b

theorem sol_b:
  (x:S) -> R S P1 P2 x -> P1 x := by

  intro x z
  have p := c5ex8.sol S P1 P2 -- c5ex8 shows that p -> q -> p
  exact z P1 p

theorem sol_c:
  (x:S) -> R S P1 P2 x -> P2 x := by

  intro x z
  have p := aux S P1 P2 -- aux shows that p -> q -> q
  exact z P2 p

end c6ex10
