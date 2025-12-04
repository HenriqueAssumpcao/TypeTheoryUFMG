-- If you want to define your own identity type (e.g., for Type Theory exercises):

inductive MyEq {α : Type u} : α → α → Type u where
  | refl (a : α) : MyEq a a

-- The induction principle for MyEq type is
-- ind-eqₐ : P(a, reflₐ) →  Π(x:A). Π(p:a=x). P(x,p) giving
-- ind_eqₐ(u,a,relfₐ) = u

def ind_eq {α : Type u} (A : α) (a : A) (P a (refl a) : Type)

-- You can add notation
notation:50 a " ≡ " b => MyEq a b

-- Prove basic properties
def myEq_symm {α : Type u} {a b : α} : (a ≡ b) → (b ≡ a) :=
  fun t =>
    match t with
    | MyEq.refl _ => MyEq.refl a

def myEq_trans {α : Type u} {a b c : α} : (a ≡ b) → (b ≡ c) → (a ≡ c)
  | MyEq.refl _, MyEq.refl _ => MyEq.refl a
