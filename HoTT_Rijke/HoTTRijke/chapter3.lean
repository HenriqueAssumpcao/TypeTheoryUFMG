namespace chapter3_naturals

-- Naturals now start at 1 (base constructor), so `myN.zero` represents 1.
inductive myN where
  | one : myN   -- represents 1
  | succ : myN → myN

deriving DecidableEq  -- Decids x = y

def _1 : myN := myN.one
def _2 : myN := myN.succ _1
def _3 : myN := myN.succ _2
def _4 : myN := myN.succ _3
def _5 : myN := myN.succ _4
def _6 : myN := myN.succ _5
def _7 : myN := myN.succ _6
def _8 : myN := myN.succ _7
def _9 : myN := myN.succ _8
def _10 : myN := myN.succ _9

def toStringMyN : myN → String
  | myN.one => "1"
  | myN.succ myN.one  => "2"
  | myN.succ (myN.succ myN.one)  => "3"
  | myN.succ (myN.succ (myN.succ myN.one)) => "4"
  | myN.succ (myN.succ (myN.succ (myN.succ myN.one))) => "5"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.one)))) => "6"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.one))))) => "7"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.one)))))) => "8"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.one))))))) => "9"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.one)))))))) => "10"
  | _ => "≥11"   -- any larger number

instance : ToString myN where
  toString := toStringMyN

def myAdd (a b : myN) : myN :=
  match b with
  | myN.one => myN.succ a        -- adding 1
  | myN.succ b' => myN.succ (myAdd a b')

def myMult (a b : myN) : myN :=
  match b with
  | myN.one => a                 -- multiplying by 1
  | myN.succ b' => myAdd (myMult a b') a

-- #eval myMult _2 _3

def myExp (a b : myN) : myN :=
  match b with
  | myN.one => a                 -- a^1 = a
  | myN.succ b' => myMult (myExp a b') a

def myMin (a b : myN) : myN :=
  match a, b with
  | myN.one, _ => myN.one
  | _, myN.one => myN.one
  | myN.succ a', myN.succ b' => myN.succ (myMin a' b')

def myMax (a b : myN) : myN :=
  match a with
  | myN.one => b
  | myN.succ a' =>
    match b with
    | myN.one => a
    | myN.succ b' => myN.succ (myMax a' b')

def triangular_number (a : myN) : myN :=
  match a with
  | myN.one => myN.one          -- 1
  | myN.succ a' => myAdd (triangular_number a') a

def factorial (a : myN) : myN :=
  match a with
  | myN.one => _1
  | myN.succ a' => myMult (factorial a') a

/- This works in 0-based naturals

def binomial (a b : myN) : myN :=
  match a with
  | myN.one =>
    match b with
    | myN.one => _1
    | myN.succ _ => _1
  | myN.succ a' =>
    match b with
    | myN.one => _1
    | myN.succ b' => myAdd (binomial a' b') (binomial a' b)
-/

def binomial (a b : myN) [DecidableEq myN] : myN :=
  let c := myMin a b
  match a, b with
  | d, myN.one => d
  | myN.one, _ => myN.one   -- No zero in 1-based naturals
  | myN.succ a', myN.succ b' =>
    if c = a then           -- Needs DecidableEq to decide c = a
      binomial a' b'
    else
      myAdd (binomial a' b') (binomial a' b)

def fibonacci (n: myN) : myN :=
  match n with
  | myN.one => myN.one            -- F1 = 1
  | myN.succ myN.one => myN.one   -- F2 = 1
  | myN.succ (myN.succ n') => myAdd (fibonacci (myN.succ n')) (fibonacci n')


def div2 (n : myN) : myN :=
  match n with
  | myN.one => myN.one                        -- 1 / 2 rounded to 1 for 1-based naturals
  | myN.succ myN.one => myN.one               -- 2 / 2 = 1
  | myN.succ (myN.succ myN.one) => myN.one    -- 3 / 2 rounded to 1
  | myN.succ (myN.succ (myN.succ n')) => myAdd (div2 (myN.succ n')) myN.one

end chapter3_naturals


namespace chapter3_integers
open chapter3_naturals

def myZ := myN ⊕ (myN ⊕ Unit)

def Zneg (n : myN) : myZ := Sum.inl n
def Zpos (n : myN) : myZ := Sum.inr (Sum.inl n)
def Zzero : myZ := Sum.inr (Sum.inr ())

/- myZ is myN ⊕ (myN ⊕ Unit)
Left:
1 -> -1
2 -> -2
3 -> -3
etc...

Right-Left
(1,U) -> 1
(2,U) -> 2
(3,U) -> 3
etc...

Right-Right
U -> 0
-/

variable(U : Unit)

def __0 : myZ := (Sum.inr (Sum.inr U))

def myNatToInt (n : myN) : myZ :=
  Zpos n

def negative (n : myZ) : myZ :=
  match n with
  | Sum.inl n' => Sum.inr (Sum.inl n')
  | Sum.inr (Sum.inr ()) => Zzero
  | Sum.inr (Sum.inl n') => Sum.inl n'

def showMyZ (z : myZ) : String :=
  match z with
  | Sum.inl n =>  "-" ++ toString n
      -- negative: 0 ↦ -1, 1 ↦ -2, ...
  | Sum.inr (Sum.inl n) => toString n
      -- positive: 0 ↦ 1, 1 ↦ 2, ...
  | Sum.inr (Sum.inr _) => "0"


instance : Coe myN myZ where
  coe := myNatToInt

#check (_1 : myZ)

def predZ (z : myZ) : myZ :=
  match z with
  | Sum.inl z' => Zneg z'.succ
  | Sum.inr (Sum.inr ()) => Zneg _1
  | Sum.inr (Sum.inl n)  =>
    match n with
    | myN.one => Zzero
    | myN.succ n' => Zpos n'

#eval showMyZ (predZ (negative _2))

def succZ (z : myZ) : myZ :=
  match z with
  | Sum.inl n =>
      match n with
      | myN.one     => Zzero
      | myN.succ n'  => Zneg n'
  | Sum.inr (Sum.inl n)     => Zpos (myN.succ n)
  | Sum.inr (Sum.inr ())    => _1


end chapter3_integers

namespace chapter3_booleans

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


def double_contrapositive_iii : myNegType (myNegType (myNegType (myNegType P) → P)) :=
  fun f : myNegType (myNegType (myNegType P) → P) =>
    -- f : (((P → Empty) → Empty) → P) → Empty
    let h1 : myNegType P := fun p : P => f (fun _ => p)
    let toP : myNegType (myNegType P) → P := fun nnP => Empty.elim (nnP h1)
    f toP

end chapter3_booleans
