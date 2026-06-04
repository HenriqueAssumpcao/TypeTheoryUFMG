import HoTTRijke.chapter5_eq
import HoTTRijke.chapter5_ints

open chapter5_myeq

-- Defying naturals starting at 0

inductive N where
  | zero : N
  | succ : N → N

def myAdd (a b : N) : N :=
  match b with
  | N.zero =>  a
  | N.succ b' => N.succ (myAdd a b')


-- Some Lemmas

def left_zero_add_N  (a : N)  : myAdd N.zero a ≡ a :=
  match a with
  | N.zero => MyEq.refl _
  | N.succ a' =>
      ap N.succ  (myAdd N.zero a') a' (left_zero_add_N a')

def left_successor_law_add (a b : N) : myAdd (N.succ a) b ≡ N.succ (myAdd a b) :=
  match b with
    | N.zero => MyEq.refl _
    | N.succ b' =>
       ap N.succ (myAdd (N.succ a) b')  (N.succ (myAdd a b')) (left_successor_law_add a b')


-- Commutative of Naturals

def add_commutative(a b : N) : myAdd a b ≡ myAdd b a :=
  match b with
  | N.zero => myEq_symm (left_zero_add_N a)
  | N.succ b =>
    (ap N.succ _ _ (add_commutative a b)) •
    (myEq_symm (left_successor_law_add b a))


-- Defying integers as an inductive type

inductive Z where
  | pos : N → Z   -- [0, ∞)
  | neg : N → Z   -- (-∞, -1]

#check Z



-- Function that sends the pair (m,n) of naturals to the integer m - n

def dif (m n : N) : Z :=
  match n with
  | N.zero => Z.pos m
  | N.succ n' =>
    match m with
    | N.zero => Z.neg n
    | N.succ m' => dif m' n'


def Zsum (a b : Z) : Z :=
  match a, b with
  | Z.pos m, Z.pos n => Z.pos (myAdd m n)
  | Z.pos m, Z.neg n => dif m (N.succ n)
  | Z.neg m, Z.pos n => dif n (N.succ m)
  | Z.neg m, Z.neg n => Z.neg (N.succ (myAdd m n))

notation:100 a "+" b => Zsum a b


def Zsum_commutative (a b : Z) : (a + b) ≡ (b + a) :=
  match a, b with
  | Z.pos m, Z.pos n => ap Z.pos _ _ (add_commutative m n)
  | Z.pos _, Z.neg _ => MyEq.refl _
  | Z.neg _, Z.pos _ => MyEq.refl _
  | Z.neg m, Z.neg n => ap Z.neg _ _ (ap N.succ _ _ (add_commutative m n))
