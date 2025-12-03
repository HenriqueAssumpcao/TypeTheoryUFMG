namespace ex_1_1
variable(A A' : Type) (a : A) (t : A = A')
example :  A' := cast t a
end  ex_1_1

namespace ex_1_2
variable (A A' : Type) (a b : A) (t : A = A') (s : a = b)
example :  (cast t a = cast t b) :=
  /- congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α}
     (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂
     returns a proof that f a₁ = f a₂ -/
    congrArg (fun x => cast t x) s
end ex_1_2


namespace ex_2_1
universe u v
variable (A : Type) (B : A → Type)

-- this is how one can define a dependent function
variable (f g : (a: A) → B a)
variable(t : (a: A) → (f a = g a))
example : f = g :=
  /- Function Extensionality
  funext.{u, v} {α : Sort u} {β : α → Sort v}
  {f g : (x : α) → β x} (h : ∀ (x : α), f x = g x) : f = g -/
  funext t
end ex_2_1

namespace ex_2_2
variable (A B: Type) (f : A → B)
def id (A : Type) : A → A := fun x => x
example : id B ∘ f = f := Eq.refl f
example : f ∘ id A = f := Eq.refl f
end ex_2_2


namespace ex_2_3
variable (A B C : Type) (f : A → B)
def const (c : C) : A → C := fun _ => c
example (c : C) : (const B C c) ∘ f = (const A C c) := rfl
example (a : A) : f ∘ (const C A a) = (const C B (f a)) := rfl
end ex_2_3

namespace ex_2_4
variable (A B : Type) (C : A → B → Type) (C₁ : B → A → Type)
def swap {A B : Type} (f: A → B → Type) : B → A → Type :=
  fun b a => f a b

example (f : A → B → Type) : swap (swap f) = f :=
  rfl


end ex_2_4
