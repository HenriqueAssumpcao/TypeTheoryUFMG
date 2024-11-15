-- Chapter 5

theorem ex5_8 (S:Prop) (P:S -> Prop) (Q:S -> Prop)
 : ((x:S) -> P x -> Q x -> P x) := by

  intro x
  exact λ a : P x => λ _ : Q x => a
