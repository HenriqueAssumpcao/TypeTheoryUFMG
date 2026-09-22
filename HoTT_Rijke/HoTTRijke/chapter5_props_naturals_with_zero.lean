-- This file contains the implementation of several functions regarding
-- zero-based natural arithmetic.

import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq

namespace props_naturals_with_zero
open chapter3_naturals_with_zero
open chapter5_myeq




-- Proofs about addition on `N` --

def myAdd_zero_left  (a : myN)  : myAdd myN.zero a ≡ a :=
  match a with
  | myN.zero => MyEq.refl _
  | myN.succ a' =>
      ap myN.succ (myAdd myN.zero a') a' (myAdd_zero_left a')

def left_successor_law_add (a b : myN) : myAdd (myN.succ a) b ≡ myN.succ (myAdd a b) :=
  match b with
    | myN.zero => MyEq.refl _
    | myN.succ b' => ap myN.succ (myAdd (myN.succ a) b')  (myN.succ (myAdd a b')) (left_successor_law_add a b')

def myAdd_commutative (a b : myN) : myAdd a b ≡ myAdd b a :=
  match b with
  | myN.zero => myEq_symm (myAdd_zero_left a)
  | myN.succ b =>
    (ap myN.succ _ _ (myAdd_commutative a b)) •
    (myEq_symm (left_successor_law_add b a))





def myAdd_assoc (a b c : myN) : myAdd (myAdd a b) c ≡ myAdd a (myAdd b c) :=
  match a with
  | myN.zero =>
      calc
        myAdd (myAdd myN.zero b) c ≡ myAdd b c := ap (fun x : myN => myAdd x c) _ _ (myAdd_zero_left b)
        _ ≡ myAdd myN.zero (myAdd b c) := myEq_symm (myAdd_zero_left (myAdd b c))
  | myN.succ a =>
      calc
        myAdd (myAdd (myN.succ a) b) c ≡ myAdd (myN.succ (myAdd a b)) c := ap (fun x : myN => myAdd x c) _ _ (left_successor_law_add a b)
        _ ≡ myN.succ (myAdd (myAdd a b) c) := left_successor_law_add (myAdd a b) c
        _ ≡ myN.succ (myAdd a (myAdd b c)) := ap myN.succ _ _ (myAdd_assoc a b c)
        _ ≡ myAdd (myN.succ a) (myAdd b c) := myEq_symm (left_successor_law_add a (myAdd b c))


def myAdd_succ_right_comm (x n m : myN) :
    myAdd (myAdd x n) (myN.succ m) ≡ myAdd (myAdd x m) (myN.succ n) :=
  calc
    myAdd (myAdd x n) (myN.succ m) ≡ myN.succ (myAdd (myAdd x n) m) := MyEq.refl _
    _ ≡ myN.succ (myAdd x (myAdd n m)) := ap myN.succ _ _ (myAdd_assoc x n m)
    _ ≡ myN.succ (myAdd x (myAdd m n)) := ap (fun t : myN => myN.succ (myAdd x t)) _ _ (myAdd_commutative n m)
    _ ≡ myN.succ (myAdd (myAdd x m) n) := ap myN.succ _ _ (myEq_symm (myAdd_assoc x m n))
    _ ≡ myAdd (myAdd x m) (myN.succ n) := MyEq.refl _








-- Proofs about commutativity of multiplication on `N` --

def myMult_zero_left (a : myN) : myMult myN.zero a ≡ myN.zero :=
  match a with
  | myN.zero => MyEq.refl _
  | myN.succ a' =>
      calc
        myMult myN.zero (myN.succ a') ≡ myAdd myN.zero (myMult myN.zero a') := MyEq.refl _
        _ ≡ myAdd myN.zero myN.zero := ap (myAdd myN.zero) _ _ (myMult_zero_left a')
        _ ≡ myN.zero := myAdd_zero_left myN.zero

def myMult_succ_left (a b : myN) : (a.succ × b) ≡ (myAdd (a × b) b) :=
  match b with
  | myN.zero => MyEq.refl _
  | myN.succ b' =>
      calc
        myMult (a.succ) (myN.succ b') ≡ myAdd (myN.succ a) (myMult (myN.succ a) b') := MyEq.refl _
        _ ≡ myAdd (myN.succ a) (myAdd (a × b') b') :=
              ap (fun x : myN => myAdd (myN.succ a) x) _ _ (myMult_succ_left a b')
        _ ≡ myN.succ (myAdd a (myAdd (a × b') b')) := left_successor_law_add a (myAdd (a × b') b')
        _ ≡ myN.succ (myAdd (myAdd a (a × b')) b') := myEq_symm (ap myN.succ _ _ (myAdd_assoc a (a × b') b'))
        _ ≡ myAdd (myAdd a (a × b')) (myN.succ b') :=
              myEq_symm
                (calc
                  myAdd (myAdd a (a × b')) (myN.succ b') ≡ myAdd (myN.succ b') (myAdd a (a × b')) :=
                        myAdd_commutative (myAdd a (a × b')) (myN.succ b')
                  _ ≡ myN.succ (myAdd b' (myAdd a (a × b'))) := left_successor_law_add b' (myAdd a (a × b'))
                  _ ≡ myN.succ (myAdd (myAdd a (a × b')) b') := ap myN.succ _ _ (myAdd_commutative b' (myAdd a (a × b')))
                )
        _ ≡ myAdd (a × (myN.succ b')) (myN.succ b') := MyEq.refl _


def myMult_comm (a b : myN) : (a × b) ≡ (b × a) :=
  match b with
  | myN.zero => myEq_symm (myMult_zero_left a)
  | myN.succ b =>
    (ap (myAdd a) _ _ (myMult_comm a b) ) •
    (myAdd_commutative _ _) •
    (myEq_symm (myMult_succ_left b a))


def mult_one_left (a : myN) : myMult _1 a ≡ a :=
    calc
      myMult _1 a ≡ myAdd (myN.zero ×  a) a := myMult_succ_left myN.zero a
      _ ≡ myAdd _0 a := ap (fun x => myAdd x a) _ _ (myMult_zero_left a)
      _ ≡ a := myAdd_zero_left a

def mult_one_right (a : myN) : myMult a _1 ≡ a := (myMult_comm _ _) • (mult_one_left a)


def mult_distributive_left (a b c : myN) : myMult a (myAdd b c) ≡ myAdd (myMult a b) (myMult a c) :=
  match a with
  | myN.zero =>
      calc
        myMult _0 (b + c) ≡ _0 := myMult_zero_left (b + c)
        _ ≡ myAdd _0 _0 := myEq_symm (myAdd_zero_left _0)
        _ ≡ myAdd (myMult _0 b) _0 := ap (fun x => myAdd x _0) _0 (myMult _0 b) (myEq_symm (myMult_zero_left b))
        _ ≡ myAdd (myMult _0 b) (myMult _0 c) := ap (myAdd (myMult _0 b)) _0 (myMult _0 c) (myEq_symm (myMult_zero_left c))
  | myN.succ a' =>
      calc
        myMult (myN.succ a') (b + c) ≡ myAdd (myMult a' (b + c)) (b + c) := myMult_succ_left _ _
        _ ≡ myAdd ((a' * b) + (a' * c)) (b + c) :=
              ap (fun x => myAdd x (b + c)) _ _ (mult_distributive_left a' b c)
        _ ≡ myAdd (a' * b) (myAdd (a' * c) (b + c)) := myAdd_assoc _ _ _
        _ ≡ myAdd (a' * b) (myAdd ((a' * c) + b) c) :=
              ap (myAdd (a' * b)) _ _ (myEq_symm (myAdd_assoc _ _ _))
        _ ≡ myAdd (a' * b) (myAdd (b + (a' * c)) c) :=
              ap ((myAdd (a' * b)) ∘ fun x => myAdd x c) _ _ (myAdd_commutative _ _)
        _ ≡ myAdd (myAdd (a' * b) (b + (a' * c))) c := myEq_symm (myAdd_assoc _ _ _)
        _ ≡ myAdd (myAdd ((a' * b) + b) (a' * c)) c :=
              ap (fun x => myAdd x c) _ _ (myEq_symm (myAdd_assoc _ _ _))
        _ ≡ myAdd ((myN.succ a' * b) + (a' * c)) c :=
              ap (fun x => myAdd x c) _ _
                (ap (fun x => myAdd x (a' * c)) ((a' * b) + b) (myN.succ a' * b) (myEq_symm (myMult_succ_left _ _)))
        _ ≡ (myN.succ a' * b) + ((a' * c) + c) := myAdd_assoc _ _ _
        _ ≡ (myN.succ a' * b) + (myN.succ a' * c) :=
              ap (myAdd (myN.succ a' * b)) _ _ (myEq_symm (myMult_succ_left _ _))


-- Defiyng Min and Max on naturals --

def N_min (a b : myN) : myN :=
  match a, b with
  | myN.zero, _ => myN.zero
  | _, myN.zero => myN.zero
  | myN.succ a', myN.succ b' => myN.succ (N_min a' b')

def N_max (a b : myN) : myN :=
  match a, b with
  | myN.zero, b => b
  | a, myN.zero => a
  | myN.succ a', myN.succ b' => myN.succ (N_max a' b')



end props_naturals_with_zero
