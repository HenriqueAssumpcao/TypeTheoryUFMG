import HoTTRijke.chapter3

namespace chapter4_booleans
open chapter3_booleans

variable (P Q : Type)

def proj_rightEmpty (A B : Type) : myNegType B → ((A ⊕ B) → A) :=
  fun b : myNegType B =>
    let g : B → A := fun x : B => Empty.elim (b x)
    let f : A → A := fun x : A => x
    fun n : A ⊕ B =>
      match n with
      | Sum.inl n => f n
      | Sum.inr n => g n

def proj_leftEmpty (A B : Type) : myNegType A → ((A ⊕ B) → B) :=
  fun b : myNegType A =>
    let g : A → B := fun x : A => Empty.elim (b x)
    let f : B → B := fun x : B => x
    fun n : A ⊕ B =>
      match n with
      | Sum.inl n => g n
      | Sum.inr n => f n

def _3_c_ii : myNegType (myNegType (((P → Q) → P) → P)) :=
  fun f : myNegType (((P → Q) → P) → P) =>
    let g : P → Q := fun p : P => Empty.elim (f fun _ => p)
    let h : ((P → Q) → P) → P := fun x => x g
    f h

-- def _3_c_iii : myNegType (myNegType ((P → Q) ⊕ (Q → P))) :=

def LEM : myNegType (myNegType (P ⊕ (myNegType P))) :=   -- Exercise 3 c) iv (Almost Law of Exclude Middle)
  fun f : myNegType (Sum P (myNegType P)) =>
    let g : myNegType P := fun x : P => f (Sum.inl x)
    let h : myNegType (myNegType P) := fun x : myNegType P => f (Sum.inr x)
    h g

def _3_d_i : (P ⊕ myNegType P) → (myNegType (myNegType P) → P) :=
  fun f : P ⊕ myNegType P =>
    fun g : myNegType (myNegType P) =>
      let h : (P ⊕ myNegType P) → P := proj_rightEmpty P (myNegType P) g
      h f

def _3_d_ii : myEquiv (myNegType (myNegType (Q → P))) ((Sum P (myNegType P)) → (Q → P)) :=
  let impl :=
    fun g : (myNegType (myNegType (Q → P))) =>
      fun s : Sum P (myNegType P) =>
        match s with
        | Sum.inl s' => fun _ : Q => s'
        | Sum.inr s' =>
          fun t : Q =>
            let QP0 := fun r : Q → P => s' (r t)
            Empty.elim (g QP0)

  let conv :=
    fun f : (Sum P (myNegType P)) → (Q → P) =>
      fun f' : myNegType (Q → P) =>
        let Neg_LEM : myNegType (Sum P (myNegType P)) := fun x : Sum P (myNegType P) => f' (f x)
        LEM P Neg_LEM


  myProd.mk impl conv

def _3_e_i : myNegType (myNegType (myNegType P)) → myNegType P :=
  fun f : myNegType (myNegType (myNegType P)) =>
    fun p : P =>
      let f' := fun x : myNegType P => x p
      f f'

def _3_e_ii : myNegType (myNegType (P → myNegType (myNegType Q))) → (P → myNegType (myNegType Q)) :=
  fun f : myNegType (myNegType (P → myNegType (myNegType Q))) =>
    fun p : P =>
      fun x : myNegType Q =>
        f (fun y : P → myNegType (myNegType Q) => y p x)

def _3_e_iii : myNegType (myNegType (myProd (myNegType (myNegType P)) (myNegType (myNegType Q)))) → (myProd (myNegType (myNegType P)) (myNegType (myNegType Q))) :=
  fun f : myNegType (myNegType  (myProd  (myNegType (myNegType P)) (myNegType (myNegType Q)))) =>
    let g1 := fun x : myNegType P =>
      f (fun y : myProd (myNegType (myNegType P)) (myNegType (myNegType Q)) => proj1 y x)
    let g2 := fun x : myNegType Q =>
      f (fun y : myProd (myNegType (myNegType P)) (myNegType (myNegType Q)) => proj2 y x)

    myProd.mk g1 g2

def _3_f_i : myEquiv (myNegType (myNegType (myProd P Q))) (myProd (myNegType (myNegType P)) (myNegType (myNegType Q))) :=
  let impl :=
    fun f : myNegType (myNegType (myProd P Q)) =>
      let g1 := fun x : myNegType P =>
        f (fun y : myProd P Q => x (proj1 y))
      let g2 := fun x : myNegType Q =>
        f (fun y : myProd P Q => x (proj2 y))

      myProd.mk g1 g2

  let conv :=
    fun f : myProd (myNegType (myNegType P)) (myNegType (myNegType Q)) =>
      fun f' : myNegType (myProd P Q) =>
        let Neg_LEM := fun x : (Sum P (myNegType P)) =>
          match x with
          | Sum.inr x' => proj1 f x'
          | Sum.inl x' =>
            let Neg_LEM2 := fun y : (Sum Q (myNegType Q)) =>
              match y with
              | Sum.inr y' => proj2 f y'
              | Sum.inl y' =>
                f' (myProd.mk x' y')

            LEM Q Neg_LEM2

        LEM P Neg_LEM

  myProd.mk impl conv

def _3_f_ii : myEquiv (myNegType (myNegType (Sum P Q))) (myNegType (myProd (myNegType P) (myNegType Q))) :=
  let impl:=
    fun f : myNegType (myNegType (Sum P Q)) =>
      fun g : (myProd (myNegType P) (myNegType Q)) =>
        let f' := fun x : P ⊕ Q =>
          match x with
          | Sum.inl x' => proj1 g x'
          | Sum.inr x' => proj2 g x'
        f f'

  let conv :=
    fun f : myNegType (myProd (myNegType P) (myNegType Q)) =>
      fun g : myNegType (Sum P Q) =>
        let Neg_LEM := fun x : (Sum P (myNegType P)) =>
          match x with
          | Sum.inl x' => g (Sum.inl x')
          | Sum.inr x' =>
            let Neg_LEM2 := fun y : (Sum Q (myNegType Q)) =>
              match y with
              | Sum.inl y' => g (Sum.inr y')
              | Sum.inr y' =>
                f (myProd.mk x' y')

            LEM Q Neg_LEM2

        LEM P Neg_LEM

  myProd.mk impl conv

def _3_f_iii : myEquiv (myNegType (myNegType (P → Q))) ((myNegType (myNegType P)) → (myNegType (myNegType Q))) :=
  let impl :=
    fun f : myNegType (myNegType (P → Q)) =>
      fun g : (myNegType (myNegType P)) =>
        fun h : myNegType Q =>
          let f' := fun p : P =>
            f (fun x : P → Q => h (x p))
          g f'


  let conv :=
    fun f : (myNegType (myNegType P)) → (myNegType (myNegType Q)) =>
      fun g : myNegType (P → Q) =>
        let nQ : myNegType Q := fun x : Q => g (fun _ : P => x)
        let P0 : P → Q := fun x : P => Empty.elim (f (double_neg P x) nQ)
        g P0

  myProd.mk impl conv


end chapter4_booleans

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


def addNaturalToZ (n : myN) (z : myZ) : myZ :=
  match n with
  | myN.one => succZ z
  | myN.succ n' => succZ (addNaturalToZ n' z)


def subtractNaturalFromZ (n : myN) (z : myZ) : myZ :=
  match n with
  | myN.one => predZ z
  | myN.succ n' => predZ (subtractNaturalFromZ n' z)


def myAdd (a b : myZ) : myZ :=
  match a with
  | Sum.inr (Sum.inr _) => b

  | Sum.inr (Sum.inl _) =>
    match b with
    | Sum.inr (Sum.inr _) => a
    | Sum.inr (Sum.inl n) => addNaturalToZ n a
    | Sum.inl n => subtractNaturalFromZ n a

  | Sum.inl _ =>
      match b with
    | Sum.inr (Sum.inr _) => a
    | Sum.inr (Sum.inl n) => addNaturalToZ n a
    | Sum.inl n => subtractNaturalFromZ n a


def multNaturalWithZ (a : myZ) (b : myN) : myZ :=
  match b with
  | myN.one => a
  | myN.succ n' => myAdd a (multNaturalWithZ a n')


def myMult (a b : myZ) : myZ :=
  match b with
  | Sum.inr (Sum.inr _) => Zzero
  | Sum.inr (Sum.inl n) => multNaturalWithZ a n
  | Sum.inl n =>  negative (multNaturalWithZ a n)

end chapter4_integers
