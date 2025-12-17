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


