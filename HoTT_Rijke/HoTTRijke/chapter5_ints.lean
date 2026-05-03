import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5

namespace Integers_
open chapter3_integers
open chapter3_naturals
open chapter5_myeq
open chapter4_integers

#check myAdd

notation:40 a " + " b => chapter4_integers.myAddZ a b
notation:60 a " × " b => chapter4_integers.myMultZ a b


#check myAdd

def pred_succ_Z (a : myZ) : predZ (succZ a) ≡ a :=
  match a with
  | Sum.inl k =>
    match k with
    | myN.one => MyEq.refl _
    -- k is zero, a is -1;
    -- predZ succZ a = predZ Zzero = Zneg myN.zero
    -- alternative: ap predZ (succZ (Sum.inl myN.zero)) (Zzero) (MyEq.refl _)
    | myN.succ _ => MyEq.refl _
    -- k is s(k'); a is -(k+1)
    -- predZ succZ a = predZ Zneg k' = Zneg S(k')
    -- alternative: ap predZ (succZ (Sum.inl (myN.succ k'))) (Zneg k') (MyEq.refl _)
  | Sum.inr (Sum.inl _) => MyEq.refl _
  -- a is Zzero
  -- predZ succZ Zzero = predZ Zpos _0 = Zzero
  -- alternative: MyEq.refl (Sum.inr (Sum.inl _))
  | Sum.inr (Sum.inr _) => MyEq.refl _

variable (U : Unit)

-- Exercise 5.6

def succ_pred_Z (a : myZ) : succZ (predZ a) ≡ a :=
  match a with
  | Sum.inl _ => MyEq.refl _
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr k) =>
    match k with
    | myN.one => MyEq.refl _
    | myN.succ _ => MyEq.refl _

-- Exercise 5.7

def zero_add_right_Z (a : myZ) : (a + Zzero) ≡ a :=
  match a with
  | Sum.inl _ => MyEq.refl _
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl _) => MyEq.refl _


/- def myAdd (a b : myZ) : myZ :=
  match b with
  | Sum.inr (Sum.inr _) => a
  | Sum.inr (Sum.inl n) => addNaturalToZ n a
  | Sum.inl n => subtractNaturalFromZ n a

def addNaturalToZ (n : myN) (z : myZ) : myZ :=
  match n with
  | myN.one => succZ z
  | myN.succ n' => addNaturalToZ n' (succZ z)


def subtractNaturalFromZ (n : myN) (z : myZ) : myZ :=
  match n with
  | myN.one => predZ z
  | myN.succ n' => subtractNaturalFromZ n' (predZ z)
-/

def zero_add_left_Z  (a : myZ) : (Zzero + a) ≡ a :=
  match a with
  | Sum.inl a' =>
    match a' with
    | myN.one => MyEq.refl _
    | myN.succ a'' =>  sorry -- substractNatFromZ a'' -1 = -a
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr a') =>
    match a' with
    | myN.one => MyEq.refl _
    | myN.succ a'' => sorry


def add_commutative_Z (a b : myZ) : (a + b) ≡ (b + a) :=
  match b with
  | Sum.inl b' => sorry
  | Sum.inr (Sum.inl _) => zero_add_right_Z a • (myEq_symm (zero_add_left_Z a))
  | Sum.inr (Sum.inr b') => sorry


def add_associative_Z (a b c : myZ) : (a + (b + c)) ≡ ((a + b) + c) := sorry

def add_right_inverse (a : myZ) : (a + (negative a)) ≡ Zzero := sorry
def add_left_inverse  (a : myZ) : ((negative a) + a) ≡ Zzero := sorry

def mult_right_zero (a : myZ) : (a × Zzero) ≡ Zzero := sorry
def mult_left_zero  (a : myZ) : (Zzero × a) ≡ Zzero := sorry

def mult_right_unit (a : myZ) : (a × _1) ≡ a := sorry
def mult_left_unit  (a : myZ) : (_1 × a) ≡ a := sorry


def mult_commutative (a b : myZ) : (a × b) ≡ (b × a) := sorry
def mult_associative (a b c : myZ) : ((a × b) × c) ≡ a × (b × c) := sorry
def add_mult_right_distributive (a b c : myZ) : ((a + b) × c)  ≡ ((a × c) + (b × c)) := sorry
def add_mult_left_distributive  (a b c : myZ) : (a × (b + c) × c)  ≡ ((a × b) + (a × c)) := sorry

end Integers_
