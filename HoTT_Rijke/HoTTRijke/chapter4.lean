import HoTTRijke.chapter3

namespace chapter4_lists
variable (A B : Type)


inductive myList (A : Type) where
  | nil : myList A
  | cons : A → (myList A → myList A)

open myList

def list_string : (myList Nat) →  String :=
  fun (l : myList Nat) =>
    match l with
    | nil => ""
    | cons a l1 => String.append (list_string l1) (toString a)

def l := cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil))))


def list_length {A : Type} (l : myList A) : Nat :=
  match l with
  | nil => 0
  | cons _ l1 => list_length l1 + 1


  def nth_list {A : Type} : myList A → Nat → Option A :=
    fun l i =>
      match l with
      | nil => none
      | cons a l1 =>
        match i with
        | 0 => some a
        | Nat.succ j => nth_list l1 j

def fold_list (μ : A → (B → B)) (b : B): myList A → B :=
  fun (l : myList A) =>
  match l with
  | nil => b
  | cons a l1 => μ a ((fold_list μ b) l1)


def map_list {A B : Type} (f : A → B) : (myList A → myList B) :=
  fun (l : myList A) =>
  match l with
  | nil => nil
  | cons a l1  => cons  (f a) (map_list f l1)

def sum_list (l : myList Nat) : Nat :=
  match l with
  | nil => 0
  | cons a l1 => a + sum_list l1

def prod_list (l : myList Nat) : Nat :=
  match l with
  | nil => 1
  | cons a l1 => a * prod_list l1

def concat_list {A : Type} (l : myList A) : myList A → myList A :=
  fun (l1 : myList A) =>
  match l1 with
  | nil => l
  | cons a l1' => cons a (concat_list  l l1')

def l2 := cons 7 (cons 9 (cons 11 nil))

def flatten_list {A : Type} : myList (myList A) → myList A :=
  fun ll =>
  match ll with
  | nil => nil
  | cons a ll1 => concat_list a (flatten_list ll1)

def ll := cons l2 (cons l nil)

#eval list_string (flatten_list ll)

def reverse_list {A : Type} : myList A → myList A :=
  fun l : myList A =>
  match l with
  | nil => nil
  | cons a l1 => concat_list (cons a nil ) (reverse_list l1)

end chapter4_lists

namespace chapter4_integers
open chapter3_integers
open chapter3_naturals
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


def addNaturalToZ (n : myN) (z : myZ) : myZ :=
  match n with
  | myN.zero => z
  | myN.succ n' => addNaturalToZ n' (succZ z)


def subtractNaturalFromZ (n : myN) (z : myZ) : myZ :=
  match n with
  | myN.zero => z
  | myN.succ n' => subtractNaturalFromZ n' (predZ z)




def myAdd (a b : myZ) : myZ :=
  match b with
  | Sum.inr (Sum.inr _) => a
  | Sum.inr (Sum.inl n) => addNaturalToZ (myN.succ n) a
  | Sum.inl n => subtractNaturalFromZ (myN.succ n) a


def multNaturalWithZ (a : myZ) (b : myN) : myZ :=
  match b with
  | myN.zero => Zzero
  | myN.succ n' => myAdd a (multNaturalWithZ a n')



def myMult (a b : myZ) : myZ :=
  match b with
  | Sum.inr (Sum.inr _) => Zzero
  | Sum.inr (Sum.inl n) => multNaturalWithZ a n.succ
  | Sum.inl n =>  negative (multNaturalWithZ a n.succ)


scoped notation:40 a " + " b => myAdd  a b
scoped notation:60 a " × "  b => myMult a b

end chapter4_integers
