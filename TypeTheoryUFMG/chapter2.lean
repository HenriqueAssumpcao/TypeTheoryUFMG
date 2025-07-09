variable (α β γ: Type)
variable (a: α)

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
example : ((α → γ) → α) → (α → γ) → ( β → γ ) :=
  fun (g : (α → γ) → α) =>  (fun (a : α → γ) => fun (_ : β) => a (g a))
