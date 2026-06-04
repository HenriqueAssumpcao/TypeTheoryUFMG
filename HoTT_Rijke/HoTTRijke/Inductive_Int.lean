import HoTTRijke.chapter5_eq

-- Defying naturals starting at 0

inductive N where
  | zero : N
  | succ : N → N

def myAdd (a b : N) : N :=
  match b with
  | N.zero =>  a
  | N.succ b' => N.succ (myAdd a b')



-- Defying integers as an inductive type

inductive myInt where
  | ofNat : N → myInt   -- [0, ∞)
  | negSucc : N → myInt   -- (-∞, -1]

#check myInt
notation:100 "-"a => myInt.negSucc a
notation:100 "+"a => myInt.ofNat a



-- Function that sends the pair (m,n) of naturals to the integer m - n

def dif (m n : N) : myInt :=
  match n with
  | N.zero => + m
  | N.succ n' =>
    match m with
    | N.zero => -n
    | N.succ m' => dif m' n'


def Zsum (a b : myInt) : myInt :=
  match a, b with
  | + m, + n => + (myAdd m n)
  | + m, -n => dif m (N.succ n)
  | -m, + n => dif n (N.succ m)
  | -m, -n => -(N.succ (myAdd m n))

notation:100 a "+" b => Zsum a b

example (a b : myInt) : (a + b) ≡ (b + a) :=
  match a, b with
  | + m, + n => sorry
  | + m, -n => sorry
  | -m, +n => sorry
  | -m, -n => sorry
