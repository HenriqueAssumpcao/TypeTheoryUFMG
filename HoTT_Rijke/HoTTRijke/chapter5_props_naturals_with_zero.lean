import HoTTRijke.chapter3_naturals_with_zero
import HoTTRijke.chapter5_eq

namespace props_naturals_with_zero
open chapter3_naturals_with_zero
open chapter5_myeq


def right_one_add_N (a : myN) : myAdd a _1 ≡ myN.succ a := MyEq.refl _

def left_zero_add_N (a : myN) : myAdd _0 a ≡ a :=
  match a with
  | myN.zero => MyEq.refl _
  | myN.succ a' =>
      ap myN.succ (myAdd _0 a') a' (left_zero_add_N a')

def right_successor_law_add (a b : myN) : myAdd a (myN.succ b) ≡ myN.succ (myAdd a b) :=
  MyEq.refl _

def left_successor_law_add (a b : myN) : myAdd (myN.succ a) b ≡ myN.succ (myAdd a b) :=
  match b with
  | myN.zero => MyEq.refl _
  | myN.succ b' =>
      ap myN.succ (myAdd (myN.succ a) b') (myN.succ (myAdd a b')) (left_successor_law_add a b')

def left_one_add_N (a : myN) : myAdd _1 a ≡ myN.succ a := by
  calc
    myAdd _1 a ≡ myAdd (myN.succ _0) a := MyEq.refl _
    _ ≡ myN.succ (myAdd _0 a) := left_successor_law_add _0 a
    _ ≡ myN.succ a := ap myN.succ (myAdd _0 a) a (left_zero_add_N a)

def add_associative (a b c : myN) : myAdd (myAdd a b) c ≡ myAdd a (myAdd b c) :=
  match c with
  | myN.zero => MyEq.refl _
  | myN.succ c' =>
      ap myN.succ (myAdd (myAdd a b) c') (myAdd a (myAdd b c')) (add_associative a b c')

def add_commutative (a b : myN) : myAdd a b ≡ myAdd b a :=
  match b with
  | myN.zero => myEq_symm (left_zero_add_N a)
  | myN.succ b' =>
      (ap myN.succ (myAdd a b') (myAdd b' a) (add_commutative a b')) •
      (myEq_symm (left_successor_law_add b' a))

def mult_zero_right (a : myN) : myMult a _0 ≡ _0 :=
  MyEq.refl _

def mult_zero_left (a : myN) : myMult _0 a ≡ _0 :=
  match a with
  | myN.zero => MyEq.refl _
  | myN.succ a' =>
      calc
        myMult _0 (myN.succ a') ≡ myAdd (myMult _0 a') _0 := MyEq.refl _
        _ ≡ myAdd _0 _0 := ap (fun x => myAdd x _0) (myMult _0 a') _0 (mult_zero_left a')
        _ ≡ _0 := left_zero_add_N _0

def mult_one_left (a : myN) : myMult _1 a ≡ a :=
  match a with
  | myN.zero => MyEq.refl _
  | myN.succ a' =>
      calc
        myMult _1 (myN.succ a') ≡ myAdd (myMult _1 a') _1 := MyEq.refl _
        _ ≡ myAdd a' _1 := ap (fun x => myAdd x _1) (myMult _1 a') a' (mult_one_left a')
        _ ≡ myN.succ a' := right_one_add_N a'

def mult_one_right (a : myN) : myMult a _1 ≡ a :=
  calc
    myMult a _1 ≡ myAdd (myMult a _0) a := MyEq.refl _
    _ ≡ myAdd _0 a := ap (fun x => myAdd x a) (myMult a _0) _0 (mult_zero_right a)
    _ ≡ a := left_zero_add_N a

def mult_successor_right (a b : myN) : myMult a (myN.succ b) ≡ myAdd (myMult a b) a :=
  MyEq.refl _

def myAdd_right (a b : myN) : myN := myAdd b a

def mult_successor_left (a b : myN) : myMult (myN.succ a) b ≡ myAdd (myMult a b) b :=
  match b with
  | myN.zero => MyEq.refl _
  | myN.succ b' =>
      calc
        myMult (myN.succ a) (myN.succ b') ≡ myAdd (myMult (myN.succ a) b') (myN.succ a) := MyEq.refl _
        _ ≡ myAdd (myAdd (myMult a b') b') (myN.succ a) :=
              ap (fun x => myAdd x (myN.succ a)) _ _ (mult_successor_left a b')
        _ ≡ myAdd (myMult a b') (myAdd b' (myN.succ a)) := add_associative _ _ _
        _ ≡ myAdd (myMult a b') (myAdd a (myN.succ b')) :=
              ap (myAdd (myMult a b')) (myAdd b' (myN.succ a)) (myAdd a (myN.succ b'))
                ((right_successor_law_add b' a) •
                 (ap myN.succ (myAdd b' a) (myAdd a b') (add_commutative b' a)) •
                 (myEq_symm (right_successor_law_add a b')))
        _ ≡ myAdd (myAdd (myMult a b') a) (myN.succ b') := myEq_symm (add_associative _ _ _)
        _ ≡ myAdd (myMult a (myN.succ b')) (myN.succ b') :=
              ap (fun x => myAdd x (myN.succ b')) (myAdd (myMult a b') a) (myMult a (myN.succ b')) (MyEq.refl _)

def mult_commutative (a b : myN) : myMult a b ≡ myMult b a :=
  match b with
  | myN.zero => myEq_symm (mult_zero_left a)
  | myN.succ b' =>
      (mult_successor_right _ _) •
      (ap (myAdd_right a) (myMult a b') (myMult b' a) (mult_commutative a b')) •
      (myEq_symm (mult_successor_left b' a))

def mult_distributive_left (a b c : myN) : myMult a (myAdd b c) ≡ myAdd (myMult a b) (myMult a c) :=
  match a with
  | myN.zero =>
      calc
        myMult _0 (b + c) ≡ _0 := mult_zero_left (b + c)
        _ ≡ myAdd _0 _0 := myEq_symm (left_zero_add_N _0)
        _ ≡ myAdd (myMult _0 b) _0 := ap (fun x => myAdd x _0) _0 (myMult _0 b) (myEq_symm (mult_zero_left b))
        _ ≡ myAdd (myMult _0 b) (myMult _0 c) := ap (myAdd (myMult _0 b)) _0 (myMult _0 c) (myEq_symm (mult_zero_left c))
  | myN.succ a' =>
      calc
        myMult (myN.succ a') (b + c) ≡ myAdd (myMult a' (b + c)) (b + c) := mult_successor_left _ _
        _ ≡ myAdd ((a' * b) + (a' * c)) (b + c) :=
              ap (fun x => myAdd x (b + c)) _ _ (mult_distributive_left a' b c)
        _ ≡ myAdd (a' * b) (myAdd (a' * c) (b + c)) := add_associative _ _ _
        _ ≡ myAdd (a' * b) (myAdd ((a' * c) + b) c) :=
              ap (myAdd (a' * b)) _ _ (myEq_symm (add_associative _ _ _))
        _ ≡ myAdd (a' * b) (myAdd (b + (a' * c)) c) :=
              ap ((myAdd (a' * b)) ∘ fun x => myAdd x c) _ _ (add_commutative _ _)
        _ ≡ myAdd (myAdd (a' * b) (b + (a' * c))) c := myEq_symm (add_associative _ _ _)
        _ ≡ myAdd (myAdd ((a' * b) + b) (a' * c)) c :=
              ap (fun x => myAdd x c) _ _ (myEq_symm (add_associative _ _ _))
        _ ≡ myAdd ((myN.succ a' * b) + (a' * c)) c :=
              ap (fun x => myAdd x c) _ _
                (ap (fun x => myAdd x (a' * c)) ((a' * b) + b) (myN.succ a' * b) (myEq_symm (mult_successor_left _ _)))
        _ ≡ (myN.succ a' * b) + ((a' * c) + c) := add_associative _ _ _
        _ ≡ (myN.succ a' * b) + (myN.succ a' * c) :=
              ap (myAdd (myN.succ a' * b)) _ _ (myEq_symm (mult_successor_left _ _))

def mult_distributive_right (a b c : myN) : myMult (a + b) c ≡ myAdd (myMult a c) (myMult b c) :=
  match c with
  | myN.zero =>
      calc
        myMult (a + b) _0 ≡ _0 := mult_zero_right _
        _ ≡ myAdd _0 _0 := myEq_symm (left_zero_add_N _0)
        _ ≡ myAdd (a * _0) _0 := ap (fun x => myAdd x _0) _0 (a * _0) (myEq_symm (mult_zero_right a))
        _ ≡ myAdd (a * _0) (b * _0) := ap (myAdd (a * _0)) _0 (b * _0) (myEq_symm (mult_zero_right b))
  | myN.succ c' =>
      calc
        myMult (a + b) (myN.succ c') ≡ myAdd (myMult (a + b) c') (a + b) := mult_successor_right _ _
        _ ≡ myAdd ((a * c') + (b * c')) (a + b) :=
              ap (fun x => myAdd x (a + b)) _ _ (mult_distributive_right a b c')
        _ ≡ myAdd (a * c') (myAdd (b * c') (a + b)) := add_associative _ _ _
        _ ≡ myAdd (a * c') (myAdd ((b * c') + a) b) :=
              ap (myAdd (a * c')) _ _ (myEq_symm (add_associative _ _ _))
        _ ≡ myAdd (a * c') (myAdd (a + (b * c')) b) :=
              ap ((myAdd (a * c')) ∘ fun x => myAdd x b) _ _ (add_commutative _ _)
        _ ≡ myAdd (myAdd (a * c') (a + (b * c'))) b := myEq_symm (add_associative _ _ _)
        _ ≡ myAdd (myAdd ((a * c') + a) (b * c')) b :=
              ap (fun x => myAdd x b) _ _ (myEq_symm (add_associative _ _ _))
        _ ≡ myAdd ((a * myN.succ c') + (b * c')) b :=
              ap (fun x => myAdd x b) _ _
                (ap (fun x => myAdd x (b * c')) ((a * c') + a) (a * myN.succ c') (myEq_symm (mult_successor_right _ _)))
        _ ≡ (a * myN.succ c') + ((b * c') + b) := add_associative _ _ _
        _ ≡ (a * myN.succ c') + (b * myN.succ c') :=
              ap (myAdd (a * myN.succ c')) _ _ (myEq_symm (mult_successor_right _ _))

def mult_associative (a b c : myN) : myMult (myMult a b) c ≡ myMult a (myMult b c) :=
  match c with
  | myN.zero => myEq_symm (mult_zero_right _)
  | myN.succ c' =>
      calc
        myMult (a * b) (myN.succ c') ≡ myAdd ((a * b) * c') (a * b) := mult_successor_right _ _
        _ ≡ myAdd (a * (b * c')) (a * b) := ap (fun x => myAdd x (a * b)) _ _ (mult_associative a b c')
        _ ≡ a * ((b * c') + b) := myEq_symm (mult_distributive_left _ _ _)
        _ ≡ a * (b * myN.succ c') := ap (myMult a) _ _ (myEq_symm (mult_successor_right _ _))

end props_naturals_with_zero
