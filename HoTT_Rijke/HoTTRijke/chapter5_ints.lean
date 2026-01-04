import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5

namespace Integers_
open chapter3_integers
open chapter3_naturals
open chapter5_myeq
open chapter4_integers

#check myAdd

notation:40 a " + " b => chapter4_integers.myAdd a b
notation:60 a " × " b => chapter4_integers.myMult a b


#check myAdd

def pred_succ_Z (a : myZ) : predZ (succZ a) ≡ a :=
  match a with
  | Sum.inl k =>
    match k with
    | myN.zero => MyEq.refl _
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
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl k) =>
    match k with
    | myN.zero => MyEq.refl _
    | myN.succ _ => MyEq.refl _

-- Exercise 5.7

def zero_add_right_Z (a : myZ) : (a + Zzero) ≡ a :=
  match a with
  | Sum.inl _ => MyEq.refl _
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl _) => MyEq.refl _


def zero_add_left_Z  (a : myZ) : (Zzero + a) ≡ a :=
  -- helper for subtracting a natural from a negative integer
  let rec sub_neg : (n k : myN) → subtractNaturalFromZ n (Zneg k) ≡ Zneg (myAdd k n) :=
    fun n =>
      match n with
      | myN.zero => fun _ => MyEq.refl _
      | myN.succ n' =>
        fun k =>
          have ih := sub_neg n' (myN.succ k)
          have step₁ := ap Zneg (myAdd (myN.succ k) n') (myN.succ (myAdd k n')) (Naturals.left_successor_law_add k n')
          have step₂ := myEq_symm (ap Zneg (myAdd k (myN.succ n')) (myN.succ (myAdd k n')) (Naturals.right_successor_law_add k n'))
          ih • step₁ • step₂
  -- helper for adding a natural to a positive integer
  let rec add_pos : (n k : myN) → addNaturalToZ n (Zpos k) ≡ Zpos (myAdd k n) :=
    fun n =>
      match n with
      | myN.zero => fun _ => MyEq.refl _
      | myN.succ n' =>
        fun k =>
          have ih := add_pos n' (myN.succ k)
          have step₁ := ap Zpos (myAdd (myN.succ k) n') (myN.succ (myAdd k n')) (Naturals.left_successor_law_add k n')
          have step₂ := myEq_symm (ap Zpos (myAdd k (myN.succ n')) (myN.succ (myAdd k n')) (Naturals.right_successor_law_add k n'))
          ih • step₁ • step₂
  match a with
  | Sum.inl a' =>
      change subtractNaturalFromZ (myN.succ a') Zzero ≡ Zneg a'
      change subtractNaturalFromZ a' (Zneg myN.zero) ≡ Zneg a'
      have h := sub_neg a' myN.zero
      have hadd := ap Zneg (myAdd _0 a') a' (Naturals.right_unit_add_N a')
      h • hadd
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl a') =>
      change addNaturalToZ (myN.succ a') Zzero ≡ Zpos a'
      change addNaturalToZ a' (Zpos myN.zero) ≡ Zpos a'
      have h := add_pos a' myN.zero
      have hadd := ap Zpos (myAdd _0 a') a' (Naturals.right_unit_add_N a')
      h • hadd


def add_commutative_Z (a b : myZ) : (a + b) ≡ (b + a) := 
  match b with 
  | Sum.inl b' => sorry 
  | Sum.inr (Sum.inr _) => zero_add_right_Z a • (myEq_symm (zero_add_left_Z a)) 
  | Sum.inr (Sum.inl b') => sorry 


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
