-- Chapter 5

namespace c5ex8

theorem sol
  (S:Prop) (P:S -> Prop) (Q:S -> Prop) : ((x:S) -> P x -> Q x -> P x) := by

  intro x
  exact λ a : P x => λ _ : Q x => a

end c5ex8
