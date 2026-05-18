import HoTTRijke.chapter3
import HoTTRijke.chapter4
import HoTTRijke.chapter5_eq

/- This file contains the implementation of natural and integer
   arithmetic from Chapter 5 of the HoTT book. -/



open chapter3_integers
open chapter3_naturals
open chapter5_myeq
open chapter4_integers

#check myAdd



-- Exercise 5.5

namespace Naturals
open chapter3_naturals
open chapter5_myeq

scoped notation:40 a " + " b => myAdd  a b
scoped notation:60 a " × "  b => myMult a b


def right_one_add_N (a : myN) : myAdd a _1 ≡ myN.succ a := MyEq.refl _

def left_one_add_N  (a : myN)  : myAdd _1 a ≡ myN.succ a :=
  match a with
  | myN.one => MyEq.refl _
  | myN.succ a' =>
      ap myN.succ  (myAdd _1 a') (myN.succ a') (left_one_add_N a')


def right_successor_law_add (a b : myN) : myAdd a (myN.succ b) ≡ myN.succ (myAdd a b) :=
  MyEq.refl _


def left_successor_law_add (a b : myN) : myAdd (myN.succ a) b ≡ myN.succ (myAdd a b) :=
  match b with
    | myN.one => MyEq.refl _
    | myN.succ b' =>
       ap myN.succ (myAdd (myN.succ a) b')  (myN.succ (myAdd a b')) (left_successor_law_add a b')


def add_associative(a b c : myN) : myAdd (myAdd a b) c ≡ myAdd a (myAdd b c) :=
  match c with
    | myN.one => MyEq.refl _
    | myN.succ c' =>
       ap myN.succ (myAdd (myAdd a b) c') (myAdd a (myAdd b c')) (add_associative a b c')


def add_commutative(a b : myN) : myAdd a b ≡ myAdd b a :=
  have comm_one : myAdd a _1 ≡ myAdd _1 a :=
    match a with
    | myN.one => MyEq.refl (_1 + _1)
    | myN.succ a' =>
      (left_successor_law_add a' _1) •
      (ap myN.succ (myAdd a' _1) (myAdd _1 a') (add_commutative a' _1)) •
      myEq_symm (right_successor_law_add _1 a')
  match b with
    | myN.one => comm_one
    | myN.succ b' =>
      (right_successor_law_add a b') •
      (ap myN.succ (myAdd a b') (myAdd b' a) (add_commutative a b')) •
      myEq_symm (left_successor_law_add b' a)


-- def mult_zero_right (a : myN) : myMult a _0 ≡ _0 :=
--   MyEq.refl _0


/- def mult_zero_left (a : myN) : myMult _0 a  ≡ _0 :=
  match a with
  | myN.zero => MyEq.refl _0
  | myN.succ a' =>
    (add_commutative (myMult _0 a') _0) •
    (ap (myAdd _0) (myMult _0 a') _0 (mult_zero_left a')) •
    (right_unit_add_N _0)
-/

def mult_one_left (a : myN) : myMult _1 a ≡ a :=
  match a with
  | myN.one => MyEq.refl _1
  -- 1 * S(a') = 1 * a' + 1 = a' + 1 = S(a')
  | myN.succ a' =>
    (add_commutative (myMult _1 a') _1) •
    (ap (myAdd _1) (myMult _1 a') a' (mult_one_left a')) •
    (left_one_add_N a')

def mult_one_right (a : myN) : myMult a _1 ≡ a :=
  -- a * 1 = a * 0 + a = 0 + a = a
  MyEq.refl _

def mult_successor_right  (a b : myN) : myMult a (myN.succ b) ≡ myAdd (myMult a b) a :=
  MyEq.refl _

def myAdd_right (a b : myN) : myN := myAdd b a

def mult_successor_left (a b : myN) : myMult (myN.succ a) b ≡ myAdd (myMult a b) b :=
  match b with
    -- S(a)*0 = 0 =  a*0 = a*0 + 0:= :=
  | myN.one => MyEq.refl _
  -- S(a)*S(b') = S(a)*b' + S(a) = (a*b' + b') + S(a) = a*b' + (b' + S(a)) =
  -- a*b' + (S(a) + b') =  a*b' + (a + S(b')) = (a*b' + a) + S(b') = a*S(b') + S(b')
  | myN.succ b' =>
  -- S(a)*b' + S(a)
  ap (fun x => myAdd x a.succ) (myMult a.succ b') (myAdd (myMult a b') b') (mult_successor_left _ _) •
  -- (a*b' + b') + S(a)
  add_associative _ _ _ •
  -- a*b' + (b'  +S(a))
  ap (myAdd (myMult a b')) (myAdd b' a.succ) (myAdd b' a).succ (right_successor_law_add _ _) •
  -- a*b' + S(b' + a)
  ap (myAdd (myMult a b')) (myAdd b' a).succ (myAdd b'.succ a) (myEq_symm (left_successor_law_add _ _)) •
  -- a*b' + (S(b') + a)
  ap (myAdd (myMult a b')) (myAdd b'.succ a) (myAdd a b'.succ) (add_commutative _ _) •
  -- a*b' + (a+S(b'))
  myEq_symm (add_associative _ _ _)  •
  -- (a*b'+ a)+S(b')
  ap (myAdd_right b'.succ) (myAdd (myMult a b') a) (myMult a b'.succ) (MyEq.refl _)


def mult_commutative (a b : myN) : (myMult a b) ≡ (myMult b a) :=
  match b with
  | myN.one => (mult_one_right _) • (myEq_symm (mult_one_left _))
  | myN.succ b' =>
  -- a * S(b') = a * b' + a = b' * a + a = S(b) * a
  mult_successor_right _ _ •
  -- a * b' + a
  ap (myAdd_right a) (myMult a b') (myMult b' a) (mult_commutative _ _) •
  -- b' * a + a
  myEq_symm (mult_successor_left _ _)


  def mult_distributive_left (a b c : myN) : (a × (b + c)) ≡ ((a × b) + (a × c)) :=
    match a with
    | myN.one =>
      mult_one_left (b + c) •
      ap (myAdd b) c (myN.one × c) (myEq_symm (mult_one_left c)) •
      ap (myAdd_right (myN.one × c)) b (myN.one × b) (myEq_symm (mult_one_left b))

    -- 0 * (b+c) = 0 = 0 + 0 = 0*b + 0 = 0*b + 0*c
    | myN.succ a' =>
    -- S(a')(b+c) = a'(b+c) + (b+c) = (a'b + a'c) + (b + c) = a'b + ((a'c + b) + c) =
    -- a'b + ((b + a'c)) + c) = a'b + ((b + a'c) + c) = (a'b + (b + a'c)) + c = ((a'b + b)+a'c) + c = (a'b + b) + (a'c + c) = S(a')*b + S(a')c
    mult_successor_left _ _ •
    -- a'(b+c) + (b+c)
    (ap (myAdd_right (myAdd b c)) (a' × (b + c)) ((a' × b) + (a' × c)) (mult_distributive_left _ _ _)) •
    -- (a'b + a'c) + (b + c)
    (add_associative _ _ _) •
    -- a'b + (a'c + (b + c))
    ap (myAdd (myMult a' b)) ((a' × c) + (b + c)) (((a' × c) + b) + c) (myEq_symm (add_associative _ _ _)) •
    -- a'b + ((a'c + b) + c)
    ap ((myAdd (myMult a' b)) ∘ (myAdd_right c)) ((a' × c) + b) (b + (a' × c)) (add_commutative _ _) •
    -- (a' × b) _+ ((b + (a × c)) + c)
    ap (myAdd (a' × b)) ((b + (a' × c)) + c) (b + ((a' × c) + c)) (add_associative _ _ _) •
    -- (a' × b) _+ (b + ((a × c)) + c))
    myEq_symm (add_associative _ _ _) •
    -- ((a' × b) + b) + ((a × c)) + c))
    ap (myAdd_right ((a' × c) + c)) ((a' × b) + b) (a'.succ × b) (myEq_symm (mult_successor_left _ _)) •
    -- a × b + ((a × c)) + c))
    ap (myAdd (a'.succ × b))  ((a' × c) + c) (a'.succ × c) (myEq_symm (mult_successor_left _ _))


def mult_distributive_right (a b c : myN) : ((a + b) × c) ≡ (a × c) + (b × c) :=
  match c with
  | myN.one =>
    (mult_one_right _) • (myEq_symm (mult_one_right _))
  | myN.succ b' =>
    -- (a + b) * S(b') = (a + b) * b' + (a + b)
    mult_successor_right _ _ •
    -- (a + b) * b' + (a + b) = (a*b' + b*b') + (a + b)
    ap (myAdd_right (a + b)) ((a + b) × b') ((a × b') + (b × b')) (mult_distributive_right a b b') •
    -- (a*b' + b*b') + (a + b)
    add_associative _ _ _ •
    -- a*b' + (b*b' + (a + b))
    ap (myAdd (a × b')) ((b × b') + (a + b)) (((b × b') + a) + b) (myEq_symm (add_associative _ _ _)) •
    -- a*b' + ((b*b' + a) + b)
    ap ((myAdd (a × b')) ∘ (myAdd_right b)) ((b × b') + a) (a + (b × b')) (add_commutative _ _) •
    -- a*b' + ((a + b*b') + b)
    myEq_symm (add_associative _ _ _) •
    -- (a*b' + (a + b*b')) + b
    ap (myAdd_right b) ((a × b') + (a + (b × b'))) (((a × b') + a) + (b × b')) (myEq_symm (add_associative _ _ _)) •
    -- ((a*b' + a) + b*b') + b
    ap (fun x => (x + (b × b')) + b) ((a × b') + a) (a × b'.succ) (myEq_symm (mult_successor_right _ _)) •
    -- (a*S(b') + b*b') + b
    add_associative _ _ _ •
    -- a*S(b') + (b*b' + b)
    ap (myAdd (a × b'.succ)) ((b × b') + b) (b × b'.succ) (myEq_symm (mult_successor_right _ _))
  -- (a+b)S(c) = (a+b)c + (a+b) = (ac + bc) + (a + b) = ac + (bc + (a + b)) =
  -- ac + ((bc + a) + b) = ac + ((a + bc) + b) = (ac + (a+bc)) + b =
  -- ((ac + a) + bc) + b = (aS(c) + bc) + b = aS(c) + (bc + b) = aS(c) + bS(c)


def mult_associative (a b c : myN) : ((a × b) × c) ≡ (a × (b × c)) :=
  match c with
  | myN.one => (mult_one_right _)
  | myN.succ c' =>
  -- (ab)c = (ab)c' + ab = a(bc')+ab = a(bc'+b) = a(bc)
    mult_successor_right _ _ •
    ap (myAdd_right (a × b)) ((a × b) × c') (a × (b × c')) (mult_associative _ _ _) •
    myEq_symm (mult_distributive_left _ _ _) •
    ap (myMult a) ((b × c') + b) (b × c'.succ) (myEq_symm (mult_successor_right _ _))

end Naturals

namespace Integers
open chapter3_naturals
open chapter3_integers
open chapter5_myeq
open chapter4_integers


notation:40 a " + " b => chapter4_integers.myAddZ a b
notation:60 a " × " b => chapter4_integers.myMultZ a b


def right_equiv_add (x : myZ) (p : a ≡ b) : myAddZ x a ≡ myAddZ x b :=
  ap (fun y => (myAddZ x y)) a b p

def left_equiv_add (x : myZ) (p : a ≡ b) : myAddZ a x ≡ myAddZ b x :=
  ap (fun y => (myAddZ y x)) a b p


-- Exercise 5.6

def succ_pred_elim (k : myZ) : succZ (predZ k) ≡ k :=
  match k with
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr (myN.succ _)) => MyEq.refl _
  | Sum.inr (Sum.inr myN.one) => MyEq.refl _
  | Sum.inl (myN.succ _) => MyEq.refl _
  | Sum.inl (myN.one) => MyEq.refl _

def pred_succ_elim (k : myZ) : predZ (succZ k) ≡ k :=
  match k with
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr (myN.succ _)) => MyEq.refl _
  | Sum.inr (Sum.inr myN.one) => MyEq.refl _
  | Sum.inl (myN.succ _) => MyEq.refl _
  | Sum.inl (myN.one) => MyEq.refl _

def pred_succ_symm (z : myZ) := pred_succ_elim z • myEq_symm (succ_pred_elim z)
def succ_pred_symm (z : myZ) := succ_pred_elim z • myEq_symm (pred_succ_elim z)

-- Exercise 5.7
-- a)


def right_add_zero (x : myZ) : (myAddZ x Zzero) ≡ x := MyEq.refl _

def zero_add_left_neg (n : myN) : (Zzero + Sum.inl n) ≡ Sum.inl n :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
      calc
        (Zzero + Sum.inl (myN.succ n')) ≡ predZ (Zzero + Sum.inl n') := MyEq.refl _
        _ ≡ predZ (Sum.inl n') := ap predZ (Zzero + Sum.inl n') (Sum.inl n') (zero_add_left_neg n')
        _ ≡ Sum.inl (myN.succ n') := MyEq.refl _


def zero_add_left_pos (n : myN) : (Zzero + Sum.inr (Sum.inr n)) ≡ Sum.inr (Sum.inr n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
      calc
        (Zzero + Sum.inr (Sum.inr (myN.succ n'))) ≡ succZ (Zzero + Sum.inr (Sum.inr n')) := MyEq.refl _
        _ ≡ succZ (Sum.inr (Sum.inr n')) := ap succZ (Zzero + Sum.inr (Sum.inr n')) (Sum.inr (Sum.inr n')) (zero_add_left_pos n')
        _ ≡ Sum.inr (Sum.inr (myN.succ n')) := MyEq.refl _


def zero_add_left_Z (a : myZ) : (Zzero + a) ≡ a :=
  match a with
  | Sum.inl n => zero_add_left_neg n
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr n) => zero_add_left_pos n


-- b)

def addNtoZ_left_pred_law (n: myN) (z : myZ) : addNaturalToZ n (predZ z) ≡ predZ (addNaturalToZ n z) :=
  match n with
  | myN.one => succ_pred_symm z
  | myN.succ n' => by
    have h : succZ (addNaturalToZ n' (predZ z)) ≡ succZ (predZ (addNaturalToZ n' z)) :=
      ap succZ _ _ (addNtoZ_left_pred_law n' z)
    exact h • myEq_symm (pred_succ_symm (addNaturalToZ n' z))

def subNfromZ_left_pred_law (n: myN) (z : myZ) : subtractNaturalFromZ n (predZ z) ≡ predZ (subtractNaturalFromZ n z) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (subNfromZ_left_pred_law n' z)


def addNtoZ_left_succ_law (n: myN) (z : myZ) : addNaturalToZ n (succZ z) ≡ succZ (addNaturalToZ n z) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => by
    have h : succZ (addNaturalToZ n' (succZ z)) ≡ succZ (succZ (addNaturalToZ n' z)) :=
      ap succZ _ _ (addNtoZ_left_succ_law n' z)
    exact h

def subNfromZ_left_succ_law (n: myN) (z : myZ) : subtractNaturalFromZ n (succZ z) ≡ succZ (subtractNaturalFromZ n z) :=
  match n with
  | myN.one => pred_succ_symm z
  | myN.succ n' => ap predZ _ _ (subNfromZ_left_succ_law n' z) • (pred_succ_symm (subtractNaturalFromZ n' z))

def left_pred_law (x y : myZ) : myAddZ (predZ x) y ≡ predZ (myAddZ x y) :=
  match y with
  | Sum.inr (Sum.inl _) => (right_add_zero (predZ x)) • (myEq_symm (ap predZ (myAddZ x Zzero) x (right_add_zero x)))
  | Sum.inl y' => subNfromZ_left_pred_law y' x
  | Sum.inr (Sum.inr y') => addNtoZ_left_pred_law y' x

def right_pred_law (x y : myZ) : myAddZ x (predZ y) ≡ predZ (myAddZ x y) :=
  match y with
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inl _ => MyEq.refl _
  | Sum.inr (Sum.inr myN.one) => myEq_symm (pred_succ_elim x)
  | Sum.inr (Sum.inr (myN.succ n)) => myEq_symm (pred_succ_elim (myAddZ x (Sum.inr (Sum.inr n))))


def right_succ_law (x y : myZ) : myAddZ x (succZ y) ≡ succZ (myAddZ x y) :=
  match y with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inl myN.one => myEq_symm (succ_pred_elim x)
  | Sum.inl (myN.succ n) => myEq_symm (succ_pred_elim (myAddZ x (Sum.inl n)))

def left_succ_law (x y : myZ) : myAddZ (succZ x) y ≡ succZ (myAddZ x y) :=
  match y with
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr n) => addNtoZ_left_succ_law n x
  | Sum.inl n => subNfromZ_left_succ_law n x


-- c)

def addNtoZ_associative (n : myN) (x y : myZ) : addNaturalToZ n (myAddZ x y) ≡ myAddZ x (addNaturalToZ n y) :=
  match n with
  | myN.one => myEq_symm (right_succ_law x y)
  | myN.succ n' => (ap succZ _ _ (addNtoZ_associative n' x y)) • myEq_symm (right_succ_law x (addNaturalToZ n' y))

def subNfromZ_associative (n : myN) (x y : myZ) : subtractNaturalFromZ n (myAddZ x y) ≡ myAddZ x (subtractNaturalFromZ n y) :=
  match n with
  | myN.one => myEq_symm (right_pred_law x y)
  | myN.succ n' => (ap predZ _ _ (subNfromZ_associative n' x y)) • myEq_symm (right_pred_law x (subtractNaturalFromZ n' y))


def left_add_one_toZpos (n : myN) :  myAddZ (Sum.inr (Sum.inr myN.one)) (Sum.inr (Sum.inr n)) ≡ succZ (Sum.inr (Sum.inr n)) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap succZ _ _ (left_add_one_toZpos n')

def left_add_one_toZneg (n : myN) :  myAddZ (Sum.inr (Sum.inr myN.one)) (Sum.inl n) ≡ succZ (Sum.inl n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (left_add_one_toZneg n') • pred_succ_symm (Sum.inl n')

def left_sub_one_toZpos (n : myN) :  myAddZ (Sum.inl myN.one) (Sum.inr (Sum.inr n)) ≡ predZ (Sum.inr (Sum.inr n)) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap succZ _ _ (left_sub_one_toZpos n') • succ_pred_symm (Sum.inr (Sum.inr n'))

def left_sub_one_toZneg (n : myN) :  myAddZ (Sum.inl myN.one) (Sum.inl n) ≡ predZ (Sum.inl n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (left_sub_one_toZneg n')

def left_add_one (z : myZ) : myAddZ (Sum.inr (Sum.inr myN.one)) z ≡ succZ z :=
  match z with
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr z') => left_add_one_toZpos z'
  | Sum.inl z' => left_add_one_toZneg z'

def left_sub_one (z : myZ) : myAddZ (Sum.inl myN.one) z ≡ predZ z :=
  match z with
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inr (Sum.inr z') => left_sub_one_toZpos z'
  | Sum.inl z' => left_sub_one_toZneg z'

def addNtoZ_commutative (n : myN) (z : myZ) : addNaturalToZ n z ≡ myAddZ (Sum.inr (Sum.inr n)) z :=
  match n with
  | myN.one => myEq_symm (left_add_one z)
  | myN.succ n' => ap succZ _ _ (addNtoZ_commutative n' z) • myEq_symm (left_succ_law (Sum.inr (Sum.inr n')) z)

def subNfromZ_commutative (n : myN) (z : myZ) : subtractNaturalFromZ n z ≡ myAddZ (Sum.inl n) z :=
  match n with
  | myN.one => myEq_symm (left_sub_one z)
  | myN.succ n' =>  ap predZ _ _ (subNfromZ_commutative n' z) • myEq_symm (left_pred_law (Sum.inl n') z)


-- d)

def addNtoZ_inverse (n : myN) : addNaturalToZ n (Sum.inl n) ≡ Zzero :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
    (addNtoZ_left_pred_law n'.succ (Sum.inl n')) •
    (pred_succ_elim (addNaturalToZ n' (Sum.inl n'))) •
    (addNtoZ_inverse n')

def subNfromZ_inverse (n : myN) : subtractNaturalFromZ n (Sum.inr (Sum.inr n)) ≡ Zzero :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
    (subNfromZ_left_succ_law n'.succ (Sum.inr (Sum.inr n'))) •
    (succ_pred_elim (subtractNaturalFromZ n' (Sum.inr (Sum.inr n')))) •
    (subNfromZ_inverse n')

--Exercise 5.8

-- a)

def multNatWithZero (n : myN) : multNaturalWithZ Zzero n ≡ Zzero :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => zero_add_left_Z (multNaturalWithZ Zzero n') • (multNatWithZero n')

def multNatWithOne (n : myN) : multNaturalWithZ (Sum.inr (Sum.inr myN.one)) n ≡ Sum.inr (Sum.inr n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
  left_add_one (multNaturalWithZ (Sum.inr (Sum.inr myN.one)) n') •
  (ap succZ _ _ (multNatWithOne n'))


variable (U : Unit)

-- Exercise 5.6
-- see succ_pred_elim



def add_commutative_Z (a b : myZ) : (a + b) ≡ (b + a) :=
  match b with
  | Sum.inl b' => subNfromZ_commutative b' a 
  | Sum.inr (Sum.inl _) => Integers.right_add_zero a • (myEq_symm (zero_add_left_Z a))
  | Sum.inr (Sum.inr b') => addNtoZ_commutative b' a  


def add_associative_Z (a b c : myZ) : (a + (b + c)) ≡ ((a + b) + c) := 
  match c with 
  | Sum.inl c' => 
    calc 
      (a + b + (Sum.inl c')) ≡ (a + (subtractNaturalFromZ c' b)) := MyEq.refl _ 
      _ ≡ (subtractNaturalFromZ c' (a + b)) := sorry 
      _  ≡ ((a+b) + Sum.inl c')  := MyEq.refl _ 
  | Sum.inr (Sum.inl _) => MyEq.refl _ 
  | Sum.inr (Sum.inr c') => sorry    

def add_right_inverse (a : myZ) : (a + (negative a)) ≡ Zzero := 
  match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    
 

def add_left_inverse  (a : myZ) : ((negative a) + a) ≡ Zzero := 
  match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    


def mult_right_zero (a : myZ) : (a × Zzero) ≡ Zzero := 
    match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    


def mult_left_zero  (a : myZ) : (Zzero × a) ≡ Zzero := 
    match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    


def mult_right_unit (a : myZ) : (a × _1) ≡ a := 
    match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    


def mult_left_unit  (a : myZ) : (_1 × a) ≡ a := 
    match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    


def mult_commutative (a b : myZ) : (a × b) ≡ (b × a) := 
    match a with 
  | Sum.inl a' => sorry
  | Sum.inr (Sum.inl _) => sorry 
  | Sum.inr (Sum.inr a') => sorry    


def mult_associative (a b c : myZ) : ((a × b) × c) ≡ a × (b × c) := sorry
def add_mult_right_distributive (a b c : myZ) : ((a + b) × c)  ≡ ((a × c) + (b × c)) := sorry
def add_mult_left_distributive  (a b c : myZ) : (a × (b + c) × c)  ≡ ((a × b) + (a × c)) := sorry

end Integers
