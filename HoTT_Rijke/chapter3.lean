namespace chapter3

inductive myN where
  | zero : myN
  | succ : myN → myN


def _0 : myN := myN.zero
def _1 : myN := myN.succ _0
def _2 : myN := myN.succ _1
def _3 : myN := myN.succ _2
def _4 : myN := myN.succ _3
def _5 : myN := myN.succ _4
def _6 : myN := myN.succ _5
def _7 : myN := myN.succ _6
def _8 : myN := myN.succ _7
def _9 : myN := myN.succ _8

def myAdd (a b : myN) : myN :=
  match b with
  | myN.zero => a
  | myN.succ b => myN.succ (myAdd a b)

def myMult (a b : myN) : myN :=
  match b with
  | myN.zero => myN.zero
  | myN.succ b => myAdd (myMult a b) a

-- #eval myMult _2 _3

def myExp (a b : myN) : myN :=
  match b with
  | myN.zero => myN.succ myN.zero
  | myN.succ b => myMult (myExp a b) a

def myMin (a b : myN) : myN :=
  match b with
  | myN.zero => b
  | myN.succ c => myN.succ (myMin a c)

def myMax (a b : myN) : myN :=
  match a with
  | myN.zero => b
  | myN.succ a' =>
    match b with
    | myN.zero => a
    | myN.succ b' => myN.succ (myMax a' b')

def triangular_number (a : myN) : myN :=
  match a with
  | myN.zero => myN.zero
  | myN.succ a' => myAdd (triangular_number a') a

def factorial (a : myN) : myN :=
  match a with
  | myN.zero => _1
  | myN.succ a' => myMult (factorial a') a


def binomial (a b : myN) : myN :=
  match a with
  | myN.zero =>
  match b with
    | myN.zero => _1
    | myN.succ _ => _0
  | myN.succ a' =>
  match b with
    | myN.zero => _1
    | myN.succ b' => myAdd (binomial a' b') (binomial a' b)


def fibonacci (n: myN) : myN :=
  match n with
  | myN.zero => myN.zero
  | myN.succ myN.zero => myN.succ myN.zero
  | myN.succ (myN.succ n) => myAdd (fibonacci (myN.succ n)) (fibonacci n)

def div2 (n : myN) : myN :=
  match n with
  | myN.zero => myN.zero
  | myN.succ myN.zero => myN.zero
  | myN.succ (myN.succ n') => myAdd (div2 n') (myN.succ myN.zero)

#eval div2 _6

def myN_ext := Sum myN Unit
/- myZ is myN ⊕ (myN ⊕ Unit)
Left:
0 -> -1
1 -> -2
2 -> -3
etc...

Right-Left
(0,U) -> 1
(1,U) -> 2
(2,U) -> 3
etc...

Right-Right
U -> 0
-/

def myZ := Sum myN myN_ext

variable(U : Unit)

#check (Sum.inl _1 : myN_ext)


def in_pos  := (fun (x : myN) => (Sum.inr (Sum.inl x : myN_ext) : myZ))
def in_zero := (fun (x : Unit) => (Sum.inr (Sum.inr x : myN_ext) : myZ))
def in_neg  := (fun (x : myN) => (Sum.inl x : myZ))

def predZ (x : myZ) : myZ :=
  match x with
  | Sum.inr (Sum.inr _) => Sum.inl _0
  | Sum.inl x =>
    match x with
    | myN.zero => Sum.inl _1
    | myN.succ x' => Sum.inl (myN.succ (myN.succ x'))
  | Sum.inr (Sum.inl x) =>
    match x with
    | myN.zero => Sum.inr (Sum.inr U)
    | myN.succ x' => Sum.inr (Sum.inl x')

inductive myBool where
  | myTrue  : myBool
  | myFalse : myBool

open myBool

def myNeg (x : myBool) : myBool :=
  match x with
  | myTrue  => myFalse
  | myFalse => myTrue

def myConj(x y : myBool) : myBool :=
  match x with
  | myFalse => myFalse
  | myTrue =>
    match y with
    | myFalse => myFalse
    | myTrue => myTrue

def myDisj(x y : myBool) : myBool :=
  match x with
  | myTrue => myTrue
  | myFalse =>
    match y with
    | myTrue => myTrue
    | myFalse => myFalse


inductive myProd (P Q : Type)
  | mk (x: P) (y: Q)

variable (P Q : Type) (z : Prod P Q)

-- Accessors for components of a value z : myProd P Q
-- Example: pattern matching directly

def proj1 {P Q : Type} (z : myProd P Q) : P :=
  match z with
  | myProd.mk x _ => x

def proj2 {P Q : Type} (z : myProd P Q) : Q :=
  match z with
  | myProd.mk _ y => y


def myProdFunc {P Q R : Type} (f : P → Q → R) : (myProd P Q → R) :=
  fun (z : myProd P Q) => f (proj1 z) (proj2 z)

#check myProdFunc

def myEquiv (P Q : Type) : Type := myProd (P → Q) (Q → P)
def myNegType  : Type := P → Empty


example (P : Type) : myNegType (myProd P (myNegType P)):=
  myProdFunc (fun (x : P) (y : P → Empty)  => y x)

example (P : Type) : myNegType (myEquiv P (myNegType P)) :=
  myProdFunc fun (f: P → myNegType P) (g: myNegType P → P) =>
    let q := fun p' => f p' p'    -- q : P -> 0
      let p := g q                -- p : P
      f p p                       -- Empty

def double_neg : (P → myNegType (myNegType P)) :=
  fun (p : P) => fun f => f p


def double_contrapositive : (P → Q) → (myNegType (myNegType P) → myNegType (myNegType Q)) := 
  fun (f : P → Q) => 
    fun (g : myNegType (myNegType P)) => 
      fun (h : myNegType Q) => 
        g (h ∘ f) 

def double_contrapositive_ii : (P → myNegType (myNegType Q)) → (myNegType (myNegType P) → myNegType (myNegType Q)) := 
  fun  f : P → myNegType (myNegType Q) =>
    -- have P -> ((Q -> 0) -> 0)
    fun g : myNegType (myNegType P) =>
      -- have (P -> 0) -> 0 
      fun h : myNegType Q =>
        -- need function P -> 0 
        have z : myNegType P := fun (p : P) => f p h 
        g z 
         
        





end chapter3
