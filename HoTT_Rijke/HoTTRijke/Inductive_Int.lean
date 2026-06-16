-- Minimal inductive integers for exercises --

import HoTTRijke.chapter5_eq

open chapter5_myeq

inductive N where
  | zero : N
  | succ : N → N

/- Integers represented as `pos n` (0,1,2,...) and `neg n` (-1,-2,...) -/
inductive Z where
  | pos : N → Z
  | neg : N → Z

/-- Negation on our `Z` type. 0 maps to 0, `pos (succ n)` to `neg n`, and `neg n` to `pos (succ n)` --/
def Negative (z : Z) : Z :=
  match z with
  | Z.pos N.zero => Z.pos N.zero
  | Z.pos (N.succ n) => Z.neg n
  | Z.neg n => Z.pos (N.succ n)

/- Notation convenience -/
notation:50 "-" z => Negative z

/- Addition on `N` (structural recursion on the second arg) -/
def myAdd (a b : N) : N :=
  match b with
  | N.zero => a
  | N.succ b' => N.succ (myAdd a b')

def myMult (a b : N) : N :=
  match b with
  | N.zero => N.zero
  | N.succ b' => myAdd a (myMult a b')

notation:70 a "×" b => myMult a b

/- Difference helper: interpret `m - n` as an integer -/
def dif (m n : N) : Z :=
  match n with
  | N.zero => Z.pos m
  | N.succ n' =>
    match m with
    | N.zero => Z.neg n'
    | N.succ m' => dif m' n'

/- Addition on `Z` using `myAdd` and `dif` -/
def Zsum (a b : Z) : Z :=
  match a, b with
  | Z.pos m, Z.pos n => Z.pos (myAdd m n)
  | Z.pos m, Z.neg n => dif m (N.succ n)
  | Z.neg m, Z.pos n => dif n (N.succ m)
  | Z.neg m, Z.neg n => Z.neg (N.succ (myAdd m n))

notation:100 a "+" b => Zsum a b


/- Multiplication: multiply an integer by a natural, then extend to `Z × Z` -/
def Z_multby_N : N → Z → Z
  | N.zero, _ => Z.pos N.zero
  | N.succ n, z => (Z_multby_N n z) + z

def Zmult (a b : Z) : Z :=
  match a with
  | Z.pos n => Z_multby_N n b
  | Z.neg n => Negative (Z_multby_N (N.succ n) b)

notation:40 a "*" b => Zmult a b


/- Proofs about addition on `N` -/

def left_zero_add_N  (a : N)  : myAdd N.zero a ≡ a :=
  match a with
  | N.zero => MyEq.refl _
  | N.succ a' =>
      ap N.succ (myAdd N.zero a') a' (left_zero_add_N a')

def left_successor_law_add (a b : N) : myAdd (N.succ a) b ≡ N.succ (myAdd a b) :=
  match b with
    | N.zero => MyEq.refl _
    | N.succ b' => ap N.succ (myAdd (N.succ a) b')  (N.succ (myAdd a b')) (left_successor_law_add a b')

def add_commutative(a b : N) : myAdd a b ≡ myAdd b a :=
  match b with
  | N.zero => myEq_symm (left_zero_add_N a)
  | N.succ b =>
    (ap N.succ _ _ (add_commutative a b)) •
    (myEq_symm (left_successor_law_add b a))


/- Commutativity for integer addition -/
def Zsum_commutative (a b : Z) : (a + b) ≡ (b + a) :=
  match a, b with
  | Z.pos m, Z.pos n => ap Z.pos _ _ (add_commutative m n)
  | Z.pos _, Z.neg _ => MyEq.refl _
  | Z.neg _, Z.pos _ => MyEq.refl _
  | Z.neg m, Z.neg n => ap Z.neg _ _ (ap N.succ _ _ (add_commutative m n))


def Z_multby_N_nat : N → N → N
  | N.zero, _ => N.zero
  | N.succ n, m => myAdd (Z_multby_N_nat n m) m


def Z_multby_N_pos_nat (n m : N) : Z_multby_N n (Z.pos m) ≡ Z.pos (Z_multby_N_nat n m) :=
  match n with
  | N.zero => MyEq.refl _
  | N.succ n =>
      calc
        Z_multby_N (N.succ n) (Z.pos m) ≡ (Z_multby_N n (Z.pos m)) + Z.pos m := MyEq.refl _
        _ ≡ Z.pos (Z_multby_N_nat n m) + Z.pos m := ap (fun x : Z => x + Z.pos m) _ _ (Z_multby_N_pos_nat n m)
        _ ≡ Z.pos (myAdd (Z_multby_N_nat n m) m) := MyEq.refl _
        _ ≡ Z.pos (Z_multby_N_nat (N.succ n) m) := MyEq.refl _


def myAdd_assoc (a b c : N) : myAdd (myAdd a b) c ≡ myAdd a (myAdd b c) :=
  match a with
  | N.zero =>
      calc
        myAdd (myAdd N.zero b) c ≡ myAdd b c := ap (fun x : N => myAdd x c) _ _ (left_zero_add_N b)
        _ ≡ myAdd N.zero (myAdd b c) := myEq_symm (left_zero_add_N (myAdd b c))
  | N.succ a =>
      calc
        myAdd (myAdd (N.succ a) b) c ≡ myAdd (N.succ (myAdd a b)) c := ap (fun x : N => myAdd x c) _ _ (left_successor_law_add a b)
        _ ≡ N.succ (myAdd (myAdd a b) c) := left_successor_law_add (myAdd a b) c
        _ ≡ N.succ (myAdd a (myAdd b c)) := ap N.succ _ _ (myAdd_assoc a b c)
        _ ≡ myAdd (N.succ a) (myAdd b c) := myEq_symm (left_successor_law_add a (myAdd b c))


def myAdd_succ_right_comm (x n m : N) :
    myAdd (myAdd x n) (N.succ m) ≡ myAdd (myAdd x m) (N.succ n) :=
  calc
    myAdd (myAdd x n) (N.succ m) ≡ N.succ (myAdd (myAdd x n) m) := MyEq.refl _
    _ ≡ N.succ (myAdd x (myAdd n m)) := ap N.succ _ _ (myAdd_assoc x n m)
    _ ≡ N.succ (myAdd x (myAdd m n)) := ap (fun t : N => N.succ (myAdd x t)) _ _ (add_commutative n m)
    _ ≡ N.succ (myAdd (myAdd x m) n) := ap N.succ _ _ (myEq_symm (myAdd_assoc x m n))
    _ ≡ myAdd (myAdd x m) (N.succ n) := MyEq.refl _


def Z_multby_N_nat_succ_right (n m : N) : Z_multby_N_nat n (N.succ m) ≡ myAdd (Z_multby_N_nat n m) n :=
  match n with
  | N.zero => MyEq.refl _
  | N.succ n =>
      calc
        Z_multby_N_nat (N.succ n) (N.succ m) ≡ myAdd (Z_multby_N_nat n (N.succ m)) (N.succ m) := MyEq.refl _
        _ ≡ myAdd (myAdd (Z_multby_N_nat n m) n) (N.succ m) := ap (fun x : N => myAdd x (N.succ m)) _ _ (Z_multby_N_nat_succ_right n m)
        _ ≡ myAdd (myAdd (Z_multby_N_nat n m) m) (N.succ n) := myAdd_succ_right_comm (Z_multby_N_nat n m) n m
        _ ≡ myAdd (Z_multby_N_nat (N.succ n) m) (N.succ n) := MyEq.refl _


def Z_multby_N_nat_zero_right (n : N) : Z_multby_N_nat n N.zero ≡ N.zero :=
  match n with
  | N.zero => MyEq.refl _
  | N.succ n =>
      calc
        Z_multby_N_nat (N.succ n) N.zero ≡ myAdd (Z_multby_N_nat n N.zero) N.zero := MyEq.refl _
        _ ≡ myAdd N.zero N.zero := ap (fun x : N => myAdd x N.zero) _ _ (Z_multby_N_nat_zero_right n)
        _ ≡ N.zero := left_zero_add_N N.zero


def Z_multby_N_nat_comm (n m : N) : Z_multby_N_nat n m ≡ Z_multby_N_nat m n :=
  match n with
  | N.zero => myEq_symm (Z_multby_N_nat_zero_right m)
  | N.succ n =>
      calc
        Z_multby_N_nat (N.succ n) m ≡ myAdd (Z_multby_N_nat n m) m := MyEq.refl _
        _ ≡ myAdd (Z_multby_N_nat m n) m := ap (fun x : N => myAdd x m) _ _ (Z_multby_N_nat_comm n m)
        _ ≡ Z_multby_N_nat m (N.succ n) := myEq_symm (Z_multby_N_nat_succ_right m n)


def Z_multby_N_pos_nat_comm (n m : N) : Z_multby_N n (Z.pos m) ≡ Z_multby_N m (Z.pos n) :=
  calc
    Z_multby_N n (Z.pos m) ≡ Z.pos (Z_multby_N_nat n m) := Z_multby_N_pos_nat n m
    _ ≡ Z.pos (Z_multby_N_nat m n) := ap Z.pos _ _ (Z_multby_N_nat_comm n m)
    _ ≡ Z_multby_N m (Z.pos n) := myEq_symm (Z_multby_N_pos_nat m n)


def Zpos_neg_add_neg (p n : N) :
    (Negative (Z.pos p) + Z.neg n) ≡ Negative (Z.pos (myAdd p (N.succ n))) :=
  match p with
  | N.zero =>
      calc
        (Negative (Z.pos N.zero) + Z.neg n) ≡ (Z.pos N.zero + Z.neg n) := MyEq.refl _
        _ ≡ Z.neg n := MyEq.refl _
        _ ≡ Negative (Z.pos (N.succ n)) := MyEq.refl _
        _ ≡ Negative (Z.pos (myAdd N.zero (N.succ n))) :=
              myEq_symm (ap Negative _ _ (ap Z.pos _ _ (left_zero_add_N (N.succ n))))
  | N.succ p =>
      calc
        (Negative (Z.pos (N.succ p)) + Z.neg n) ≡ (Z.neg p + Z.neg n) := MyEq.refl _
        _ ≡ Z.neg (N.succ (myAdd p n)) := MyEq.refl _
        _ ≡ Z.neg (myAdd (N.succ p) n) := myEq_symm (ap Z.neg _ _ (left_successor_law_add p n))
        _ ≡ Negative (Z.pos (myAdd (N.succ p) (N.succ n))) := MyEq.refl _


def Z_multby_N_neg_pos (a n : N) :
    Z_multby_N a (Z.neg n) ≡ Negative (Z_multby_N a (Z.pos (N.succ n))) :=
  match a with
  | N.zero => MyEq.refl _
  | N.succ a =>
      calc
        Z_multby_N (N.succ a) (Z.neg n) ≡ (Z_multby_N a (Z.neg n)) + Z.neg n := MyEq.refl _
        _ ≡ Negative (Z_multby_N a (Z.pos (N.succ n))) + Z.neg n :=
              ap (fun x : Z => x + Z.neg n) _ _ (Z_multby_N_neg_pos a n)
        _ ≡ Negative (Z.pos (Z_multby_N_nat a (N.succ n))) + Z.neg n :=
              ap (fun x : Z => x + Z.neg n) _ _ (ap Negative _ _ (Z_multby_N_pos_nat a (N.succ n)))
        _ ≡ Negative (Z.pos (myAdd (Z_multby_N_nat a (N.succ n)) (N.succ n))) :=
              Zpos_neg_add_neg (Z_multby_N_nat a (N.succ n)) n
        _ ≡ Negative (Z_multby_N (N.succ a) (Z.pos (N.succ n))) :=
              ap Negative _ _ (myEq_symm (Z_multby_N_pos_nat (N.succ a) (N.succ n)))


def Neg_rule (z : Z) : Negative (Negative z) ≡ z :=
  match z with
  | Z.pos N.zero => MyEq.refl _
  | Z.pos (N.succ _) => MyEq.refl _
  | Z.neg _ => MyEq.refl _


def Zmult_commutative (a b : Z) : Zmult a b ≡ Zmult b a :=
  match a, b with
  | Z.pos a, Z.pos b =>
      Z_multby_N_pos_nat_comm a b
  | Z.pos a, Z.neg b =>
      calc
        Zmult (Z.pos a) (Z.neg b) ≡ Z_multby_N a (Z.neg b) := MyEq.refl _
        _ ≡ Negative (Z_multby_N a (Z.pos (N.succ b))) := Z_multby_N_neg_pos a b
        _ ≡ Negative (Z_multby_N (N.succ b) (Z.pos a)) :=
              ap Negative _ _ (Z_multby_N_pos_nat_comm a (N.succ b))
        _ ≡ Zmult (Z.neg b) (Z.pos a) := MyEq.refl _
  | Z.neg a, Z.pos b =>
      calc
        Zmult (Z.neg a) (Z.pos b) ≡ Negative (Z_multby_N (N.succ a) (Z.pos b)) := MyEq.refl _
        _ ≡ Negative (Z_multby_N b (Z.pos (N.succ a))) :=
              ap Negative _ _ (myEq_symm (Z_multby_N_pos_nat_comm b (N.succ a)))
        _ ≡ Zmult (Z.pos b) (Z.neg a) := myEq_symm (Z_multby_N_neg_pos b a)
  | Z.neg a, Z.neg b =>
      calc
        Zmult (Z.neg a) (Z.neg b) ≡ Negative (Z_multby_N (N.succ a) (Z.neg b)) := MyEq.refl _
        _ ≡ Negative (Negative (Z_multby_N (N.succ a) (Z.pos (N.succ b)))) :=
              ap Negative _ _ (Z_multby_N_neg_pos (N.succ a) b)
        _ ≡ Negative (Negative (Z_multby_N (N.succ b) (Z.pos (N.succ a)))) :=
              ap Negative _ _ (ap Negative _ _ (Z_multby_N_pos_nat_comm (N.succ a) (N.succ b)))
        _ ≡ Negative (Z_multby_N (N.succ b) (Z.neg a)) :=
              myEq_symm (ap Negative _ _ (Z_multby_N_neg_pos (N.succ b) a))
        _ ≡ Zmult (Z.neg b) (Z.neg a) := MyEq.refl _
