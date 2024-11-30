-- OBS:
-- α can be typed in VSCode by \a
-- λ can be typed in VSCode by \fun
-- → can be typed in VSCode by \r
-- ↦ can be typed in VSCode by \mapsto
-- ... for more info just hover the symbol with the mouse

namespace ChurchNumerals

universe u

-- Define Type for Church Numerals (Nat is defined in Lean already)
def Num := (α : Type u) → (α → α) → α → α

#check Num

-- Define basic numerals
def Zero  : Num := λ α ↦ λ _ : α → α ↦ λ x : α ↦ x
def One   : Num := λ α ↦ λ f : α → α ↦ λ x : α ↦ f x
def Two   : Num := λ α ↦ λ f : α → α ↦ λ x : α ↦ f (f x)
def Three : Num := λ α ↦ λ f : α → α ↦ λ x : α ↦ f (f (f x))

-- Checking the types
#check Zero
#check Zero Nat
#check Zero Nat (λ n ↦ n + 1)
#check Zero Nat (λ n ↦ n + 1) 0
-- Computing a value
def eval : Num → Nat := λ cn ↦ cn Nat (λ n ↦ n + 1) 0
#eval eval Zero
#eval eval One
#eval eval Two

-- Succ expression
def Suc : Num → Num :=
    λ n : Num ↦
    λ β : Type ↦
    λ f : β → β ↦
    λ x : β ↦
    f (n β f x)

#check Suc

-- Examples
#eval eval (Suc Zero)
#eval eval (Suc One)
#eval eval (Suc (Suc One))

-- Add expression
def Add : Num → Num → Num :=
    λ m n : Num ↦
    λ α : Type ↦
    λ f : α → α ↦
    λ x : α ↦
    m α f (n α f x)

#eval eval (Add One One)
#eval eval (Add Two Two)
#eval eval (Add Three Three)

def Add' : Num → Num → Num :=
    λ m n ↦ λ α ↦ λ f ↦ λ x ↦
    (n _ Suc (m _ Suc Zero)) α f x

#eval eval (Add' One One)
#eval eval (Add' Two Two)
#eval eval (Add' Three Three)

-- Mult expression
def Mult : Num → Num → Num :=
    λ m n : Num ↦
    λ α : Type ↦
    λ f : α → α ↦
    λ x : α ↦
    m α (n α f) x

#eval eval (Mult Two Three)
#eval eval (Mult Three Three)

-- Power operation
def Pow : Num → Num → Num :=
  λ b e : Num ↦
  λ α ↦
    e (α → α) (b α)

#eval eval (Pow Two Three)
#eval eval (Pow Three Three)

-- Predecessor (Suc⁻¹)
def Pred : Num → Num :=
  λ n α f x ↦
    n ((α → α) → α)
      (λ g : (α → α) → α ↦
       λ h : α → α ↦ h (g f))
      (λ _ : α → α ↦ x)
      (λ u : α ↦ u)

#eval eval (Pred Zero)
#eval eval (Pred One)
#eval eval (Pred Two)

-- Subtraction expression
def Sub : Num → Num → Num :=
    λ m n ↦ λ α ↦ λ f ↦ λ x ↦
      (n _ Pred (m _ Suc Zero)) α f x
-- SUB := λm.λn.n PRED m,

#eval eval (Sub Zero Zero) = 0
#eval eval (Sub One One) = 0
#eval eval (Sub One Zero) = 1
#eval eval (Sub Two Zero) = 2
#eval eval (Sub Two One) = 1
#eval eval (Sub Two Two) = 0
#eval eval (Sub Three Zero) = 3
#eval eval (Sub Three One) = 2
#eval eval (Sub Three Two) = 1
#eval eval (Sub Three Three) = 0

-- Define church booleans (Bool already defined in Lean)
def Bol := (α : Type) → α → α → α

def True  : Bol := λ α : Type ↦ λ x _ : α ↦ x
def False : Bol := λ α : Type ↦ λ _ y : α ↦ y

def evalBol : Bol → Bool :=
    λ b : Bol ↦
        b Bool true false

#eval evalBol True
#eval evalBol False

def Neg : Bol → Bol :=
  λ b : Bol ↦
  λ α : Type ↦
  λ x y : α ↦
    b α y x

#eval evalBol (Neg True)
#eval evalBol (Neg False)

def And : Bol → Bol → Bol :=
  λ p q : Bol ↦
  λ α : Type ↦
    p (α → α → α) (q α) (p α)

#eval evalBol (And True True)
#eval evalBol (And True False)
#eval evalBol (And False True)
#eval evalBol (And False False)

def Or : Bol → Bol → Bol :=
  λ p q : Bol ↦
  λ α : Type ↦
    p (α → α → α) (p α) (q α)

#eval evalBol (Or True True)
#eval evalBol (Or True False)
#eval evalBol (Or False True)
#eval evalBol (Or False False)

def IfThenElse : Bol → Bol :=
  λ p : Bol ↦
  λ α : Type ↦
  λ a b : α ↦
    p α a b

-- Iszero expression
def Iszero : Num → Bol :=
    λ z : Num ↦
    λ α : Type ↦
    λ x y : α ↦
      z α (λ _ ↦ y) x

-- Alternative expression, same meaning
def Iszero' : Num → Bol :=
    λ z : Num ↦
    λ α : Type ↦
      z (α → α → α) (λ _ ↦ False α) (True α)

#eval evalBol (Iszero Zero)
#eval evalBol (Iszero' Zero)
#eval evalBol (Iszero One)
#eval evalBol (Iszero' One)
#eval evalBol (Iszero Two)
#eval evalBol (Iszero' Two)


-- <= expression
-- LEQ := λm.λn.ISZERO (SUB m n),

end ChurchNumerals
