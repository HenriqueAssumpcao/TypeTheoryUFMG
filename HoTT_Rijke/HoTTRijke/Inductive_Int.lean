import HoTTRijke.chapter5_eq

open chapter5_myeq



-- Defying naturals starting at 0

inductive N where
  | zero : N
  | succ : N → N

def myAdd (a b : N) : N :=
  match b with
  | N.zero =>  a
  | N.succ b' => N.succ (myAdd a b')


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
    | N.zero => Z.neg n'
    | N.succ m' => dif m' n'

-- Defying Sum of Integers

def Zsum (a b : Z) : Z :=
  match a, b with
  | Z.pos m, Z.pos n => Z.pos (myAdd m n)
  | Z.pos m, Z.neg n => dif m (N.succ n)
  | Z.neg m, Z.pos n => dif n (N.succ m)
  | Z.neg m, Z.neg n => Z.neg (N.succ (myAdd m n))

notation:100 a "+" b => Zsum a b

-- Defying the Simetric of an Integer

def Negative (z : Z) : Z :=
  match z with
  | Z.pos z => Z.neg z
  | Z.neg z => Z.pos z


-- Defying Multiplication of Integers

def Z_multby_N (n : N) (z : Z) : Z :=
  match n with
  | N.zero => Z.pos (N.zero)
  | N.succ n => (Z_multby_N n z) + z

def Zmult (a b : Z) : Z :=
  match a with
  | Z.pos a => Z_multby_N a b
  | Z.neg a => Negative (Z_multby_N a b)


-- Defying the sucessor of an Integer

def SuccZ (z : Z) : Z := z + Z.pos (N.succ N.zero)

def Succ_rule (n : N) : SuccZ (Z.pos n) ≡ Z.pos (N.succ n) :=
  match n with
  | N.zero => MyEq.refl _
  | N.succ n => ap SuccZ _  _ (myEq_symm (Succ_rule n))





-- Proving that the sum of Integers is commutative


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


def add_commutative(a b : N) : myAdd a b ≡ myAdd b a :=
  match b with
  | N.zero => myEq_symm (left_zero_add_N a)
  | N.succ b =>
    (ap N.succ _ _ (add_commutative a b)) •
    (myEq_symm (left_successor_law_add b a))



def Zsum_commutative (a b : Z) : (a + b) ≡ (b + a) :=
  match a, b with
  | Z.pos m, Z.pos n => ap Z.pos _ _ (add_commutative m n)
  | Z.pos _, Z.neg _ => MyEq.refl _
  | Z.neg _, Z.pos _ => MyEq.refl _
  | Z.neg m, Z.neg n => ap Z.neg _ _ (ap N.succ _ _ (add_commutative m n))







-- Proving that multiplication of Integers is commutative

def Zsum_zero (a : Z) : (a + (Z.pos N.zero)) ≡ a :=
  match a with
  | Z.pos _ => MyEq.refl _
  | Z.neg _ => MyEq.refl _

def Z_multby_zero (z : N) : Z_multby_N z (Z.pos N.zero) ≡ Z.pos N.zero :=
  match z with
  | N.zero => MyEq.refl _
  | N.succ z =>
    calc
      ((Z_multby_N z (Z.pos N.zero)) + (Z.pos N.zero)) ≡ (Z_multby_N z (Z.pos N.zero)) := Zsum_zero (Z_multby_N z (Z.pos N.zero))
      _ ≡ Z.pos N.zero := Z_multby_zero z

def Z_multby_succN (z n : N) : ((Z_multby_N z (Z.pos n)) + Z.pos z) ≡ (Z_multby_N z (SuccZ (Z.pos n))) :=
  match z with
  | N.zero => MyEq.refl _
  | N.succ z =>
    calc
      ((Z_multby_N (N.succ z) (Z.pos n)) + Z.pos (N.succ z)) ≡ SuccZ (Z_multby_N (N.succ z) (Z.pos n) + (Z.pos n)) :=sorry
      _ ≡ SuccZ (Z_multby_N z (Z.pos n) + (Z.pos n) + (Z.pos z)) := sorry
      _ ≡ (Z_multby_N (N.succ z) (SuccZ (Z.pos n))) := sorry


def Z_multby_N_commutative (n z : N) : Z_multby_N n (Z.pos z) ≡ Z_multby_N z (Z.pos n) :=
  match n with
  | N.zero => myEq_symm (Z_multby_zero z)
  | N.succ n =>
    calc
      ((Z_multby_N n (Z.pos z)) + Z.pos z) ≡ ((Z_multby_N z (Z.pos n)) + Z.pos z) := ap (fun x : Z => x + Z.pos z) _ _ (Z_multby_N_commutative n z)
      _ ≡ (Z_multby_N z (SuccZ (Z.pos n))) := Z_multby_succN z n
      _ ≡ Z_multby_N z (Z.pos (N.succ n)) := ap (fun x : Z => Z_multby_N z x) _ _ (Succ_rule n)

def mult_right_Neg (a b : Z) : Zmult a (Negative b) ≡ Negative (Zmult a b) := sorry

def mult_left_Neg (a b : Z) :  Zmult (Negative a) b ≡ Negative (Zmult a b) := sorry

def Zmult_commutative (a b : Z) : Zmult a b ≡ Zmult b a :=
  match a, b with
  | Z.pos a, Z.pos b => Z_multby_N_commutative a b
  | Z.pos a, Z.neg b =>
    calc
      Zmult (Z.pos a) (Z.neg b) ≡ Negative (Zmult (Z.pos a) (Z.pos b)) :=  mult_right_Neg (Z.pos a) (Z.pos b)
      _ ≡ Negative (Zmult (Z.pos b) (Z.pos a)) := ap Negative _ _ (Z_multby_N_commutative a b)
      _ ≡ Zmult (Z.neg b) (Z.pos a) := mult_left_Neg (Z.pos b) (Z.pos a)

  | Z.neg a, Z.pos b =>
    (mult_left_Neg (Z.pos a) (Z.pos b)) •
    (ap Negative _ _ (Z_multby_N_commutative a b)) •
    (myEq_symm (mult_right_Neg (Z.pos b) (Z.pos a)))

  | Z.neg a, Z.neg b =>
    (mult_right_Neg (Z.neg a) (Z.pos b)) •
    (ap Negative (Zmult (Z.neg a) (Z.pos b)) (Negative (Zmult (Z.pos a) (Z.pos b))) (mult_left_Neg (Z.pos a) (Z.pos b))) •
    (ap (fun x : Z => Negative (Negative x)) _ _ (Z_multby_N_commutative a b)) •
    (ap Negative _  _ (myEq_symm (mult_left_Neg (Z.pos b) (Z.pos a)))) •
    (myEq_symm (mult_right_Neg (Z.neg b) (Z.pos a)))
