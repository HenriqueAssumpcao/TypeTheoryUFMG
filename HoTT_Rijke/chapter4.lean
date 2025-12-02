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
