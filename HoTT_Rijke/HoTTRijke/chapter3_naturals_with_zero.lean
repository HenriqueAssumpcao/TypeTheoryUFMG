import HoTTRijke.chapter5_eq

open chapter5_myeq

namespace chapter3_naturals_with_zero

-- Naturals now start at 1 (base constructor), so `myN.zero` represents 1.
inductive myN where
  | zero : myN   -- represents 1
  | succ : myN → myN

deriving DecidableEq  -- Decides x = y


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
def _10 : myN := myN.succ _9


def toStringMyN : myN → String
  | myN.zero => "0"
  | myN.succ myN.zero  => "1"
  | myN.succ (myN.succ myN.zero)  => "2"
  | myN.succ (myN.succ (myN.succ myN.zero)) => "3"
  | myN.succ (myN.succ (myN.succ (myN.succ myN.zero))) => "4"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.zero)))) => "5"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.zero))))) => "6"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.zero)))))) => "7"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.zero))))))) => "8"
  | myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ (myN.succ myN.zero)))))))) => "9"
  | _ => "≥10"   -- any larger number

instance : ToString myN where
  toString := toStringMyN


def myAdd (a b : myN) : myN :=
  match b with
  | myN.zero => a        -- adding 0
  | myN.succ b' => myN.succ (myAdd a b')


def myMult (a b : myN) : myN :=
  match b with
  | myN.zero => _0                 -- multiplying by 1
  | myN.succ b' => myAdd (myMult a b') a

instance : Add myN where
  add := myAdd

instance : Mul myN where
  mul := myMult

def myExp (a b : myN) : myN :=
  match b with
  | myN.zero => _1                 -- a^1 = a
  | myN.succ b' => myMult (myExp a b') a


def myMin (a b : myN) : myN :=
  match a, b with
  | myN.zero, _ => _0
  | _, myN.zero => _0
  | myN.succ a', myN.succ b' => myN.succ (myMin a' b')


def myMax (a b : myN) : myN :=
  match a with
  | myN.zero => b
  | myN.succ a' =>
    match b with
    | myN.zero => a
    | myN.succ b' => myN.succ (myMax a' b')


def triangular_number (a : myN) : myN :=
  match a with
  | myN.zero => myN.zero          -- 1
  | myN.succ a' => myAdd (triangular_number a') a


def factorial (a : myN) : myN :=
  match a with
  | myN.zero => _1
  | myN.succ a' => myMult (factorial a') a

/- There is a problem with the implementation of some of the following functions. Since
   there is no zero among naturals, binomial a b for a < b returns 1.

   One might fix this problem by
   -- introducing a new type N0 = Sum myN Unit
   -- checking if a >= b.
-/

def binomial (a b : myN) : myN :=
  match a with
  | myN.zero =>
    match b with
    | myN.zero => _0
    | myN.succ _ => _0
  | myN.succ a' =>
    match b with
    | myN.zero => _1
    | myN.succ b' => myAdd (binomial a' b') (binomial a' b)


def binomial_v2 (a b : myN) [DecidableEq myN] : myN :=
  let c := myMin a b
  match a, b with
  | _, myN.zero => _1
  | myN.zero, _ => _0   -- No zero in 1-based naturals
  | myN.succ a', myN.succ b' =>
    if c = a then           -- Needs DecidablmyAddeEq to decide c = a
      binomial a' b'
    else
      myAdd (binomial a' b') (binomial a' b)

def fibonacci (n: myN) : myN :=
  match n with
  | myN.zero => _1            -- F1 = 1
  | myN.succ myN.zero => _1   -- F2 = 1
  | myN.succ (myN.succ n') => myAdd (fibonacci (myN.succ n')) (fibonacci n')


def div2 (n : myN) : myN :=
  match n with
  | myN.zero => _0                       -- 1 / 2 rounded to 0
  | myN.succ myN.zero => _0               -- 2 / 2 = 1
  | myN.succ (myN.succ myN.zero) => _1    -- 3 / 2 rounded to 1
  | myN.succ (myN.succ (myN.succ n')) => myAdd (div2 (myN.succ n')) _1

def dist (m n : myN) : myN :=
  match m, n with
  | myN.zero, myN.zero => myN.zero
  | myN.zero, myN.succ n => myN.succ n
  | myN.succ m, myN.zero => myN.succ m
  | myN.succ m, myN.succ n => dist m n

#check dist myN.zero myN.zero

end chapter3_naturals_with_zero



namespace chapter3_propositions

open chapter3_naturals_with_zero


def Less_than (m n : myN) : Prop :=
  match m, n with
  | myN.zero, myN.zero => False
  | myN.zero, myN.succ _ => True
  | myN.succ _, myN.zero => False
  | myN.succ m, myN.succ n => Less_than m n

def Less_than_succ (n : myN) : Less_than n n.succ := by
  cases n with
  | zero => exact True.intro
  | succ n' => exact Less_than_succ n'

def Less_than_trans (m n p : myN) (h1 : Less_than m n) (h2 : Less_than n p) : Less_than m p := by
  cases m with
  | zero =>
    cases n with
    | zero => exact False.elim h1
    | succ _ =>
      cases p with
      | zero => exact False.elim h2
      | succ _ => exact True.intro

  | succ m' =>
    cases n with
    | zero => exact False.elim h1
    | succ n' =>
      cases p with
      | zero => exact False.elim h2
      | succ p' =>
        have h3 : Less_than m' n' := h1
        have h4 : Less_than n' p' := h2
        exact Less_than_trans m' n' p' h3 h4

def Less_than_irrefl (n : myN) : ¬ Less_than n n := by
  intro h
  cases n with
  | zero => exact False.elim h
  | succ n' =>
    have h1 : Less_than n' n' := h
    exact Less_than_irrefl n' h1

def Less_than_on_equals (m n : myN) (p : m ≡ n) : ¬ Less_than m n := by
  intro h                       -- When Goal is A → B, intro h assumes A and adds it to the context, then tries to prove B.
  cases p                       -- Cases for inductive types. MyEq has only one constructor refl.
  exact Less_than_irrefl m h    -- Goal now is Less_than m m, which is exactly what Less_than_irrefl m h proves.

end chapter3_propositions
