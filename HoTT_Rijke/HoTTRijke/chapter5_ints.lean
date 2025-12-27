import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5

namespace Integers_
open chapter3_integers
open chapter3_naturals
open chapter5_myeq
-- open chapter4_integers

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

#check Zzero + Zzero
#check chapter4_integers.myAdd Zzero Zzero
#check Zzero
-- def add_left_zero (a : myZ) : (a + Zzero) ≡ a := sorry
end Integers_
