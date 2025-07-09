variable (α β γ: Prop)

/-
   Exercises for chapter 2 of the book 'Type Theory and Formal Proof' by
   Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/


/-
   Exercise 2.11. Find inhabitants of the following types in the empty context, by giving
   appropriate derivations.

   (a) (α → α → γ) → α → β → γ
   (b) (α → γ) → α) → (α → γ) → β → γ
-/

-- solution for part (a)
example (g : (α → γ) → α) : (α → γ) → ( β → γ ) :=
  fun (a : α → γ) => fun (_ : β) => a (g a)


-- solution for part (b)
example : ((α → γ) → α) → (α → γ) → (β → γ) :=
  fun (g : (α → γ) → α) =>  (fun (a : α → γ) => fun (_ : β) => a (g a))

/- Exercise 2.12

(a) Construct a term of type ((α → β) → α) → ((α → (α → β)) → α)
(b) Construct a term of type ((α → β) → α) → (α → α → β) → β. Hint: use (a).
-/

-- solution for (a)

example : ((α → β) → α) → ((α → (α → β)) → α) :=
  fun (g : (α → β) → α) =>
    fun (h : α → (α → β)) =>
      g (fun a : α => (h a) a) -- this is the term of type (α → β) that g expects

-- second solution for (a) as a theorem

theorem part_a {α β : Prop} : ((α → β) → α) → ((α → (α → β)) → α) := by
  intro h
  intro g

  have  t : α → β := by
    intro a
    exact g a a

  exact h t

-- solution for (b) using (a)

example : ((α → β) → α) → (α → α → β) → β := by
   intro h
   intro g
   exact g (part_a h g) (part_a h g)
