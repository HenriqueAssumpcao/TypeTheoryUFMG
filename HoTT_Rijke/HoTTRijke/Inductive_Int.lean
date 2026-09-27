-- Minimal inductive integers for exercises --

import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_props_naturals_with_zero

open chapter5_myeq
open chapter3_naturals_with_zero
open props_naturals_with_zero

-- Integers represented as `pos n` (0,1,2,...) and `neg n` (-1,-2,...) --
inductive Z where
  | pos : myN → Z
  | neg : myN → Z

--- Negation on our `Z` type. 0 maps to 0, `pos (succ n)` to `neg n`, and `neg n` to `pos (succ n)` ---
def Negative (z : Z) : Z :=
  match z with
  | Z.pos myN.zero => Z.pos myN.zero
  | Z.pos (myN.succ n) => Z.neg n
  | Z.neg n => Z.pos (myN.succ n)

-- Notation convenience --
notation:50 "-" z => Negative z

-- Difference helper: interpret `m - n` as an integer --
def dif (m n : myN) : Z :=
  match n with
  | myN.zero => Z.pos m
  | myN.succ n' =>
    match m with
    | myN.zero => Z.neg n'
    | myN.succ m' => dif m' n'

-- Addition on `Z` using `myAdd` and `dif` --
def Zsum (a b : Z) : Z :=
  match a, b with
  | Z.pos m, Z.pos n => Z.pos (myAdd m n)
  | Z.pos m, Z.neg n => dif m (myN.succ n)
  | Z.neg m, Z.pos n => dif n (myN.succ m)
  | Z.neg m, Z.neg n => Z.neg (myN.succ (myAdd m n))

notation:100 a "+" b => Zsum a b


-- Multiplication: multiply an integer by a natural, then extend to `Z × Z` --
def Z_multby_N : myN → Z → Z
  | myN.zero, _ => Z.pos myN.zero
  | myN.succ n, z => (Z_multby_N n z) + z

def Zmult (a b : Z) : Z :=
  match a with
  | Z.pos n => Z_multby_N n b
  | Z.neg n => Negative (Z_multby_N (myN.succ n) b)

notation:40 a "*" b => Zmult a b


-- Commutativity for integer addition --
def Zsum_commutative (a b : Z) : (a + b) ≡ (b + a) :=
  match a, b with
  | Z.pos m, Z.pos n => ap Z.pos _ _ (add_commutative m n)
  | Z.pos _, Z.neg _ => MyEq.refl _
  | Z.neg _, Z.pos _ => MyEq.refl _
  | Z.neg m, Z.neg n => ap Z.neg _ _ (ap myN.succ _ _ (add_commutative m n))


def Z_multby_N_nat : myN → myN → myN
  | myN.zero, _ => myN.zero
  | myN.succ n, m => myAdd (Z_multby_N_nat n m) m


def Z_multby_N_pos_nat (n m : myN) : Z_multby_N n (Z.pos m) ≡ Z.pos (Z_multby_N_nat n m) :=
  match n with
  | myN.zero => MyEq.refl _
  | myN.succ n =>
      calc
        Z_multby_N (myN.succ n) (Z.pos m) ≡ (Z_multby_N n (Z.pos m)) + Z.pos m := MyEq.refl _
        _ ≡ Z.pos (Z_multby_N_nat n m) + Z.pos m := ap (fun x : Z => x + Z.pos m) _ _ (Z_multby_N_pos_nat n m)
        _ ≡ Z.pos (myAdd (Z_multby_N_nat n m) m) := MyEq.refl _
        _ ≡ Z.pos (Z_multby_N_nat (myN.succ n) m) := MyEq.refl _



def Z_multby_N_nat_succ_right (n m : myN) : Z_multby_N_nat n (myN.succ m) ≡ myAdd (Z_multby_N_nat n m) n :=
  match n with
  | myN.zero => MyEq.refl _
  | myN.succ n =>
      calc
        Z_multby_N_nat (myN.succ n) (myN.succ m) ≡ myAdd (Z_multby_N_nat n (myN.succ m)) (myN.succ m) := MyEq.refl _
        _ ≡ myAdd (myAdd (Z_multby_N_nat n m) n) (myN.succ m) := ap (fun x : myN => myAdd x (myN.succ m)) _ _ (Z_multby_N_nat_succ_right n m)
        _ ≡ myAdd (myAdd (Z_multby_N_nat n m) m) (myN.succ n) := myAdd_succ_right_comm (Z_multby_N_nat n m) n m
        _ ≡ myAdd (Z_multby_N_nat (myN.succ n) m) (myN.succ n) := MyEq.refl _


def Z_multby_N_nat_zero_right (n : myN) : Z_multby_N_nat n myN.zero ≡ myN.zero :=
  match n with
  | myN.zero => MyEq.refl _
  | myN.succ n =>
      calc
        Z_multby_N_nat (myN.succ n) myN.zero ≡ myAdd (Z_multby_N_nat n myN.zero) myN.zero := MyEq.refl _
        _ ≡ myAdd myN.zero myN.zero := ap (fun x : myN => myAdd x myN.zero) _ _ (Z_multby_N_nat_zero_right n)
        _ ≡ myN.zero := left_zero_add_N myN.zero


def Z_multby_N_nat_comm (n m : myN) : Z_multby_N_nat n m ≡ Z_multby_N_nat m n :=
  match n with
  | myN.zero => myEq_symm (Z_multby_N_nat_zero_right m)
  | myN.succ n =>
      calc
        Z_multby_N_nat (myN.succ n) m ≡ myAdd (Z_multby_N_nat n m) m := MyEq.refl _
        _ ≡ myAdd (Z_multby_N_nat m n) m := ap (fun x : myN => myAdd x m) _ _ (Z_multby_N_nat_comm n m)
        _ ≡ Z_multby_N_nat m (myN.succ n) := myEq_symm (Z_multby_N_nat_succ_right m n)


def Z_multby_N_pos_nat_comm (n m : myN) : Z_multby_N n (Z.pos m) ≡ Z_multby_N m (Z.pos n) :=
  calc
    Z_multby_N n (Z.pos m) ≡ Z.pos (Z_multby_N_nat n m) := Z_multby_N_pos_nat n m
    _ ≡ Z.pos (Z_multby_N_nat m n) := ap Z.pos _ _ (Z_multby_N_nat_comm n m)
    _ ≡ Z_multby_N m (Z.pos n) := myEq_symm (Z_multby_N_pos_nat m n)


def Zpos_neg_add_neg (p n : myN) :
    (Negative (Z.pos p) + Z.neg n) ≡ Negative (Z.pos (myAdd p (myN.succ n))) :=
  match p with
  | myN.zero =>
      calc
        (Negative (Z.pos myN.zero) + Z.neg n) ≡ (Z.pos myN.zero + Z.neg n) := MyEq.refl _
        _ ≡ Z.neg n := MyEq.refl _
        _ ≡ Negative (Z.pos (myN.succ n)) := MyEq.refl _
        _ ≡ Negative (Z.pos (myAdd myN.zero (myN.succ n))) :=
              myEq_symm (ap Negative _ _ (ap Z.pos _ _ (left_zero_add_N (myN.succ n))))
  | myN.succ p =>
      calc
        (Negative (Z.pos (myN.succ p)) + Z.neg n) ≡ (Z.neg p + Z.neg n) := MyEq.refl _
        _ ≡ Z.neg (myN.succ (myAdd p n)) := MyEq.refl _
        _ ≡ Z.neg (myAdd (myN.succ p) n) := myEq_symm (ap Z.neg _ _ (left_successor_law_add p n))
        _ ≡ Negative (Z.pos (myAdd (myN.succ p) (myN.succ n))) := MyEq.refl _


def Z_multby_N_neg_pos (a n : myN) :
    Z_multby_N a (Z.neg n) ≡ Negative (Z_multby_N a (Z.pos (myN.succ n))) :=
  match a with
  | myN.zero => MyEq.refl _
  | myN.succ a =>
      calc
        Z_multby_N (myN.succ a) (Z.neg n) ≡ (Z_multby_N a (Z.neg n)) + Z.neg n := MyEq.refl _
        _ ≡ Negative (Z_multby_N a (Z.pos (myN.succ n))) + Z.neg n :=
              ap (fun x : Z => x + Z.neg n) _ _ (Z_multby_N_neg_pos a n)
        _ ≡ Negative (Z.pos (Z_multby_N_nat a (myN.succ n))) + Z.neg n :=
              ap (fun x : Z => x + Z.neg n) _ _ (ap Negative _ _ (Z_multby_N_pos_nat a (myN.succ n)))
        _ ≡ Negative (Z.pos (myAdd (Z_multby_N_nat a (myN.succ n)) (myN.succ n))) :=
              Zpos_neg_add_neg (Z_multby_N_nat a (myN.succ n)) n
        _ ≡ Negative (Z_multby_N (myN.succ a) (Z.pos (myN.succ n))) :=
              ap Negative _ _ (myEq_symm (Z_multby_N_pos_nat (myN.succ a) (myN.succ n)))


def Neg_rule (z : Z) : Negative (Negative z) ≡ z :=
  match z with
  | Z.pos myN.zero => MyEq.refl _
  | Z.pos (myN.succ _) => MyEq.refl _
  | Z.neg _ => MyEq.refl _


def Zmult_commutative (a b : Z) : Zmult a b ≡ Zmult b a :=
  match a, b with
  | Z.pos a, Z.pos b =>
      Z_multby_N_pos_nat_comm a b
  | Z.pos a, Z.neg b =>
      calc
        Zmult (Z.pos a) (Z.neg b) ≡ Z_multby_N a (Z.neg b) := MyEq.refl _
        _ ≡ Negative (Z_multby_N a (Z.pos (myN.succ b))) := Z_multby_N_neg_pos a b
        _ ≡ Negative (Z_multby_N (myN.succ b) (Z.pos a)) :=
              ap Negative _ _ (Z_multby_N_pos_nat_comm a (myN.succ b))
        _ ≡ Zmult (Z.neg b) (Z.pos a) := MyEq.refl _
  | Z.neg a, Z.pos b =>
      calc
        Zmult (Z.neg a) (Z.pos b) ≡ Negative (Z_multby_N (myN.succ a) (Z.pos b)) := MyEq.refl _
        _ ≡ Negative (Z_multby_N b (Z.pos (myN.succ a))) :=
              ap Negative _ _ (myEq_symm (Z_multby_N_pos_nat_comm b (myN.succ a)))
        _ ≡ Zmult (Z.pos b) (Z.neg a) := myEq_symm (Z_multby_N_neg_pos b a)
  | Z.neg a, Z.neg b =>
      calc
        Zmult (Z.neg a) (Z.neg b) ≡ Negative (Z_multby_N (myN.succ a) (Z.neg b)) := MyEq.refl _
        _ ≡ Negative (Negative (Z_multby_N (myN.succ a) (Z.pos (myN.succ b)))) :=
              ap Negative _ _ (Z_multby_N_neg_pos (myN.succ a) b)
        _ ≡ Negative (Negative (Z_multby_N (myN.succ b) (Z.pos (myN.succ a)))) :=
              ap Negative _ _ (ap Negative _ _ (Z_multby_N_pos_nat_comm (myN.succ a) (myN.succ b)))
        _ ≡ Negative (Z_multby_N (myN.succ b) (Z.neg a)) :=
              myEq_symm (ap Negative _ _ (Z_multby_N_neg_pos (myN.succ b) a))
        _ ≡ Zmult (Z.neg b) (Z.neg a) := MyEq.refl _
