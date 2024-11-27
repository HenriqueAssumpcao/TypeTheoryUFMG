-- Chapter 5

namespace c5ex8

theorem sol
  (S:Prop) (P:S -> Prop) (Q:S -> Prop) : ((x:S) -> P x -> Q x -> P x) := by

  intro x
  exact λ a : P x => λ _ : Q x => a

end c5ex8


namespace c5ex10
-- Exercício 5.10
-- Code by Csaba

theorem ex5_10
  (S : Prop)
  (P : S → Prop)
  (f : S → S)
  (g : S → S)
  (u : (x : S) → P (f x) → P (g x))
  (v : (x y : S) → (P x → P y) → P (f x)) :
  (x : S) → P (f (f x)) := by

  intro (x : S)
  exact v (f x) (g x) (u x)
end c5ex10
