variable (α β γ: Type)
variable (a: α)


def myLambda : α → α := fun x => x
-- Solution to Exercise 11 in the book Type Theory and Formal Proof

example  : ((α → γ) → α) → (α → γ) → ( β → γ ) :=
  fun (g : (α → γ) → α) =>  (fun (a : α → γ) => fun (_ : β) => a (g a))


def  func1 (g : (α → γ) → α) : (α → γ) → ( β → γ ) :=
  fun (a : α → γ) => fun (_ : β) => a (g a)

#check func1
