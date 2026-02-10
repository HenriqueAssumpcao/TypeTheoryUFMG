import HoTTRijke.chapter3
import HoTTRijke.chapter4

namespace chapter5_myeq
universe u v w

-- If you want to define your own identity type (e.g., for Type Theory exercises):

inductive MyEq {α : Type} : α → α → Type where
  | refl (a : α) : MyEq a a

-- The induction principle for MyEq type is
-- ind-eqₐ : P(a, reflₐ) →  Π(x:A). Π(p:a=x). P(x,p) giving
-- ind_eqₐ(u,a,relfₐ) = u

-- You can add notation
notation:100 a " ≡ " b => MyEq a b


def ind_eq {α : Type} {a : α}
    (P : (x : α) → (a ≡ x) → Type) : -- P is indexed by x : α and p : a ≡ x
    (P a (MyEq.refl a)) →  ((x : α) → (p : a ≡ x) → P x p) :=
  by
    intro h x p
    cases p
    exact h


-- Prove basic properties
def myEq_symm {α : Type} {a x : α} : (a ≡ x) → (x ≡ a) := by
  intro p -- p : a ≡ x
  /- At this point we want to prove x ≡ a. The type P(x,p) is 'x ≡ a'
     independent of p. -/
  let P : (x : α) → (a ≡ x) → Type := fun x _ => (x ≡ a)

  -- P a (MyEq.refl a) is 'a = a' and 'MyEq.refl a' is proof of this.
  -- thus we apply ind_eq
  exact ind_eq (α:=α) (a:=a) P (MyEq.refl a) x p

def myEq_symm_refl {α: Type} (a : α) : myEq_symm (MyEq.refl a) ≡ (MyEq.refl a) :=
  MyEq.refl _


 def myEq_refl {α : Type} {a : α} : (a ≡ a) := MyEq.refl a

 def myEq_trans {α : Type} {a x y : α} : (a ≡ x) → (x ≡ y) → (a ≡ y):= by
  intro p
  let P : (x' : α) → (a ≡ x') → Type := fun x' _ => (x' ≡ y) → (a ≡ y)
  exact ind_eq P (fun a => a) x p

def concat_eq {α : Type} {x y z : α} : (x ≡ y) → (y ≡ z) → (x ≡ z) :=  by
  intro p
  let P : (y' : α) → (x ≡ y') → Type := fun y' _ => (y' ≡ z) → (x ≡ z)
  exact ind_eq P (fun a => a) y p

notation:60 a " • " b => concat_eq a b

def concat_assoc {α : Type} {a b c d : α} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) :
    (p • (q • r)) ≡ ((p • q) • r) := by
    cases p
    cases q
    cases r
    exact MyEq.refl _

def concat_right_unit {α : Type} {a b : α} (p : a ≡ b) : (p • (MyEq.refl b)) ≡ p := by
  cases p
  exact MyEq.refl (MyEq.refl a)

def concat_left_unit  {α : Type} {a b : α} (p : a ≡ b) : ((MyEq.refl a) • p) ≡ p := by
  cases p
  exact MyEq.refl (MyEq.refl a)


def ap {α : Type} {β : Type} (f : α → β) (x y : α) (p : x ≡ y) : (f x ≡ f y) := by
  let P : (y' : α) → (x ≡ y') → Type := fun y' _ => f x ≡ f y'
  exact ind_eq (α:=α) (a:=x) P (MyEq.refl (f x)) y p


def left_unit  {α : Type} {a b : α} (p : a ≡ b) : (a ≡ b) := (MyEq.refl a) • p
def right_unit {α : Type} {a b : α} (p : a ≡ b) : (a ≡ b) := p • MyEq.refl b

-- Exercise 5.1

def sym_contat_distributive {α : Type} {x y z : α} (p1 : x ≡ y ) (p2 : y ≡ z ) :
      myEq_symm (p1 • p2) ≡ (myEq_symm p2) • (myEq_symm p1) := by
        cases p1
        cases p2
        -- ⊢ myEq_symm (MyEq.refl x • MyEq.refl x) ≡ myEq_symm (MyEq.refl x) • myEq_symm (MyEq.refl x)
        exact
        (ap myEq_symm (MyEq.refl x • MyEq.refl x) (MyEq.refl x) (concat_right_unit (MyEq.refl x))) •
        myEq_symm_refl (x) •
        concat_right_unit (MyEq.refl x)

--Exercise 5.2

def inv_con {α : Type} {a b c : α} (p : a ≡ b) (q : b ≡ c) (r : a ≡ c) :
    ((p • q) ≡ r) → (q ≡ (myEq_symm p • r)) := by
    cases p
    cases q
    cases r
    --  ((MyEq.refl a • MyEq.refl a) ≡ MyEq.refl a) → MyEq.refl a ≡ myEq_symm (MyEq.refl a) • MyEq.refl a
    exact fun p => myEq_symm p

def con_inv {α : Type} {a b c : α} (p : a ≡ b) (q : b ≡ c) (r : a ≡ c) :
    ((p • q) ≡ r) → (p ≡ r • (myEq_symm q)) := by
    cases p
    cases q
    cases r
    --  ((MyEq.refl a • MyEq.refl a) ≡ MyEq.refl a) → MyEq.refl a ≡ myEq_symm (MyEq.refl a) • MyEq.refl a
    exact fun p => myEq_symm p


def ap_id {α : Type} (x y : α) (p : x ≡ y) : p ≡ (ap (fun (x:α) => x) x y p) := by
  let P : (y' : α) → (p' : x ≡ y') → Type := fun y' p' => p' ≡ (ap (fun (x:α) => x) x y' p')
  exact ind_eq (α:=α) (a:=x) P (MyEq.refl _) y p


/-
def ap_comp {α : Type} {β : Type} {γ : Type} (f : α → β) (g : β → γ) (x y : α) (p : x ≡ y) :
  ap g (f x) (f y) (ap f x y  p) ≡ ap (g ∘ f) x y p := by
  let t := ap  f x x (MyEq.refl x)
  let s := ap_id x x (MyEq.refl x)
  let P : (y' : α) → (p' : x ≡ y') → Type :=
    fun y' p' => ap g (f x) (f y') (ap f x y' p') ≡ ap (g ∘ f) x y' p'
  have u : P x (MyEq.refl x) := by
      cases p
      sorry
  exact ind_eq (α:=α) (a:=x) P u y p
-/

def ap_comp {α : Type} {β : Type} {γ : Type} (f : α → β) (g : β → γ) (x y : α) (p : x ≡ y) : ap g (f x) (f y) (ap f x y  p) ≡ ap (g ∘ f) x y p := by
  let P (y' : α) (p' : x ≡ y') : Type :=
    ap g (f x) (f y') (ap f x y' p') ≡ ap (g ∘ f) x y' p'

  have u : P x (MyEq.refl x) :=
    MyEq.refl (MyEq.refl (g (f x)))

  exact ind_eq (α:=α) (a:=x) P u y p

def unique_ref {α : Type} (x y : α) (p : x ≡ y) :
  (⟨x, MyEq.refl x⟩ : Σ (y' : α ), x ≡ y') ≡ ⟨y, p⟩ :=
    by
      cases p
      exact MyEq.refl _

def transport {α : Type} {x y : α} (β : (x' : α) → Type) : (x ≡ y) → (β x → β y) :=
  by
    intro p q
    let β' : (y' : α) → (x ≡ y') → Type := fun y' _ => β y'
    exact ind_eq β' q y p


-- Exercise 5.3

def lift_β (α : Type) (β : (a : α) → Type) (a x : α) (b : β a) (p : a ≡ x) :
  (⟨a, b⟩ : Σ a, β a) ≡ ⟨x, transport β p b⟩ := by
  cases p
  have q : transport β (MyEq.refl a) b  ≡ b :=
    MyEq.refl b
  exact  ap (fun c => (⟨a, c⟩ : Σ a, β a)) (transport β (MyEq.refl a) b) b q

-- Exercise 5.4

def maclane_pentagon {α : Type} (a b c d e : α) (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) : Type := by
  have α₁ : (((p • q) • r) • s) ≡ ((p • (q • r)) • s) := by
    have h := myEq_symm (concat_assoc p q r)
    let rs (p' : a ≡ d) : a ≡ e := concat_eq p' s
    have h' := ap rs ((p • q) • r) (p • (q • r)) h
    exact h'

  have α₂ : ((p • (q • r)) • s) ≡ (p • (q • r) • s) := by
    have h := myEq_symm (concat_assoc p (q • r) s)
    exact h

  have α₃ : (p • ((q • r) • s)) ≡ (p • (q • (r • s))) := by
    have h := myEq_symm (concat_assoc q r s)
    let rs (p' : b ≡ e) : a ≡ e := concat_eq p p'
    have h' := ap rs ((q • r) • s) (q • (r • s)) h
    exact h'

  have α₄ : (((p • q) • r) • s) ≡ ((p • q) • (r • s)) := by
    have h := myEq_symm (concat_assoc (p • q) r s)
    exact h

  have α₅ : ((p • q) • (r • s)) ≡ (p • (q • (r • s))) := by
    have h := myEq_symm (concat_assoc p q (r • s))
    exact h

  have t : ((α₁ • α₂) • α₃) ≡ (α₄ • α₅) := by
    induction s
    induction r
    induction q
    induction p
    cases ((α₁ • α₂) • α₃)
    cases α₄ • α₅
    exact MyEq.refl (MyEq.refl (((MyEq.refl a • MyEq.refl a) • MyEq.refl a) • MyEq.refl a))

  exact α

end chapter5_myeq

-- Exercise 5.5

namespace Naturals
open chapter3_naturals
open chapter5_myeq

scoped notation:40 a " + " b => myAdd  a b
scoped notation:60 a " × "  b => myMult a b


def right_one_add_N (a : myN) : myAdd a _1 ≡ myN.succ a := MyEq.refl _

def left_one_add_N  (a : myN)  : myAdd _1 a ≡ myN.succ a :=
  match a with
  | myN.one => MyEq.refl _
  | myN.succ a' =>
      ap myN.succ  (myAdd _1 a') (myN.succ a') (left_one_add_N a')


def right_successor_law_add (a b : myN) : myAdd a (myN.succ b) ≡ myN.succ (myAdd a b) :=
  MyEq.refl _


def left_successor_law_add (a b : myN) : myAdd (myN.succ a) b ≡ myN.succ (myAdd a b) :=
  match b with
    | myN.one => MyEq.refl _
    | myN.succ b' =>
       ap myN.succ (myAdd (myN.succ a) b')  (myN.succ (myAdd a b')) (left_successor_law_add a b')


def add_associative(a b c : myN) : myAdd (myAdd a b) c ≡ myAdd a (myAdd b c) :=
  match c with
    | myN.one => MyEq.refl _
    | myN.succ c' =>
       ap myN.succ (myAdd (myAdd a b) c') (myAdd a (myAdd b c')) (add_associative a b c')


def add_commutative(a b : myN) : myAdd a b ≡ myAdd b a :=
  have comm_one : myAdd a _1 ≡ myAdd _1 a :=
    match a with
    | myN.one => MyEq.refl (_1 + _1)
    | myN.succ a' =>
      (left_successor_law_add a' _1) •
      (ap myN.succ (myAdd a' _1) (myAdd _1 a') (add_commutative a' _1)) •
      myEq_symm (right_successor_law_add _1 a')

  match b with
    | myN.one => comm_one
    | myN.succ b' =>
      (right_successor_law_add a b') •
      (ap myN.succ (myAdd a b') (myAdd b' a) (add_commutative a b')) •
      myEq_symm (left_successor_law_add b' a)


-- def mult_zero_right (a : myN) : myMult a _0 ≡ _0 :=
--   MyEq.refl _0


/- def mult_zero_left (a : myN) : myMult _0 a  ≡ _0 :=
  match a with
  | myN.zero => MyEq.refl _0
  | myN.succ a' =>
    (add_commutative (myMult _0 a') _0) •
    (ap (myAdd _0) (myMult _0 a') _0 (mult_zero_left a')) •
    (right_unit_add_N _0)
-/

def mult_one_left (a : myN) : myMult _1 a ≡ a :=
  match a with
  | myN.one => MyEq.refl _1
  -- 1 * S(a') = 1 * a' + 1 = a' + 1 = S(a')
  | myN.succ a' =>
    (add_commutative (myMult _1 a') _1) •
    (ap (myAdd _1) (myMult _1 a') a' (mult_one_left a')) •
    (left_one_add_N a')

def mult_one_right (a : myN) : myMult a _1 ≡ a :=
  -- a * 1 = a * 0 + a = 0 + a = a
  MyEq.refl _

def mult_successor_right  (a b : myN) : myMult a (myN.succ b) ≡ myAdd (myMult a b) a := MyEq.refl _

def myAdd_right (a b : myN) : myN := myAdd b a

def mult_successor_left (a b : myN) : myMult (myN.succ a) b ≡ myAdd (myMult a b) b :=
  match b with
    -- S(a)*0 = 0 =  a*0 = a*0 + 0:= :=
  | myN.one => MyEq.refl _
  -- S(a)*S(b') = S(a)*b' + S(a) = (a*b' + b') + S(a) = a*b' + (b' + S(a)) =
  -- a*b' + (S(a) + b') =  a*b' + (a + S(b')) = (a*b' + a) + S(b') = a*S(b') + S(b')
  | myN.succ b' =>
  -- S(a)*b' + S(a)
  ap (fun x => myAdd x a.succ) (myMult a.succ b') (myAdd (myMult a b') b') (mult_successor_left _ _) •
  -- (a*b' + b') + S(a)
  add_associative _ _ _ •
  -- a*b' + (b'  +S(a))
  ap (myAdd (myMult a b')) (myAdd b' a.succ) (myAdd b' a).succ (right_successor_law_add _ _) •
  -- a*b' + S(b' + a)
  ap (myAdd (myMult a b')) (myAdd b' a).succ (myAdd b'.succ a) (myEq_symm (left_successor_law_add _ _)) •
  -- a*b' + (S(b') + a)
  ap (myAdd (myMult a b')) (myAdd b'.succ a) (myAdd a b'.succ) (add_commutative _ _) •
  -- a*b' + (a+S(b'))
  myEq_symm (add_associative _ _ _)  •
  -- (a*b'+ a)+S(b')
  ap (myAdd_right b'.succ) (myAdd (myMult a b') a) (myMult a b'.succ) (MyEq.refl _)


def mult_commutative (a b : myN) : (myMult a b) ≡ (myMult b a) :=
  match b with
  | myN.one => (mult_one_right _) • (myEq_symm (mult_one_left _))
  | myN.succ b' =>
  -- a * S(b') = a * b' + a = b' * a + a = S(b) * a
  mult_successor_right _ _ •
  -- a * b' + a
  ap (myAdd_right a) (myMult a b') (myMult b' a) (mult_commutative _ _) •
  -- b' * a + a
  myEq_symm (mult_successor_left _ _)


  def mult_distributive_left (a b c : myN) : (a × (b + c)) ≡ ((a × b) + (a × c)) :=
    match a with
    | myN.one =>
      mult_one_left (b + c) •
      ap (myAdd b) c (myN.one × c) (myEq_symm (mult_one_left c)) •
      ap (myAdd_right (myN.one × c)) b (myN.one × b) (myEq_symm (mult_one_left b))

    -- 0 * (b+c) = 0 = 0 + 0 = 0*b + 0 = 0*b + 0*c
    | myN.succ a' =>
    -- S(a')(b+c) = a'(b+c) + (b+c) = (a'b + a'c) + (b + c) = a'b + ((a'c + b) + c) =
    -- a'b + ((b + a'c)) + c) = a'b + ((b + a'c) + c) = (a'b + (b + a'c)) + c = ((a'b + b)+a'c) + c = (a'b + b) + (a'c + c) = S(a')*b + S(a')c
    mult_successor_left _ _ •
    -- a'(b+c) + (b+c)
    (ap (myAdd_right (myAdd b c)) (a' × (b + c)) ((a' × b) + (a' × c)) (mult_distributive_left _ _ _)) •
    -- (a'b + a'c) + (b + c)
    (add_associative _ _ _) •
    -- a'b + (a'c + (b + c))
    ap (myAdd (myMult a' b)) ((a' × c) + (b + c)) (((a' × c) + b) + c) (myEq_symm (add_associative _ _ _)) •
    -- a'b + ((a'c + b) + c)
    ap ((myAdd (myMult a' b)) ∘ (myAdd_right c)) ((a' × c) + b) (b + (a' × c)) (add_commutative _ _) •
    -- (a' × b) _+ ((b + (a × c)) + c)
    ap (myAdd (a' × b)) ((b + (a' × c)) + c) (b + ((a' × c) + c)) (add_associative _ _ _) •
    -- (a' × b) _+ (b + ((a × c)) + c))
    myEq_symm (add_associative _ _ _) •
    -- ((a' × b) + b) + ((a × c)) + c))
    ap (myAdd_right ((a' × c) + c)) ((a' × b) + b) (a'.succ × b) (myEq_symm (mult_successor_left _ _)) •
    -- a × b + ((a × c)) + c))
    ap (myAdd (a'.succ × b))  ((a' × c) + c) (a'.succ × c) (myEq_symm (mult_successor_left _ _))


def mult_distributive_right (a b c : myN) : ((a + b) × c) ≡ (a × c) + (b × c) :=
  match c with
  | myN.one =>
    (mult_one_right _) • (myEq_symm (mult_one_right _))
  | myN.succ b' =>
    -- (a + b) * S(b') = (a + b) * b' + (a + b)
    mult_successor_right _ _ •
    -- (a + b) * b' + (a + b) = (a*b' + b*b') + (a + b)
    ap (myAdd_right (a + b)) ((a + b) × b') ((a × b') + (b × b')) (mult_distributive_right a b b') •
    -- (a*b' + b*b') + (a + b)
    add_associative _ _ _ •
    -- a*b' + (b*b' + (a + b))
    ap (myAdd (a × b')) ((b × b') + (a + b)) (((b × b') + a) + b) (myEq_symm (add_associative _ _ _)) •
    -- a*b' + ((b*b' + a) + b)
    ap ((myAdd (a × b')) ∘ (myAdd_right b)) ((b × b') + a) (a + (b × b')) (add_commutative _ _) •
    -- a*b' + ((a + b*b') + b)
    myEq_symm (add_associative _ _ _) •
    -- (a*b' + (a + b*b')) + b
    ap (myAdd_right b) ((a × b') + (a + (b × b'))) (((a × b') + a) + (b × b')) (myEq_symm (add_associative _ _ _)) •
    -- ((a*b' + a) + b*b') + b
    ap (fun x => (x + (b × b')) + b) ((a × b') + a) (a × b'.succ) (myEq_symm (mult_successor_right _ _)) •
    -- (a*S(b') + b*b') + b
    add_associative _ _ _ •
    -- a*S(b') + (b*b' + b)
    ap (myAdd (a × b'.succ)) ((b × b') + b) (b × b'.succ) (myEq_symm (mult_successor_right _ _))
  -- (a+b)S(c) = (a+b)c + (a+b) = (ac + bc) + (a + b) = ac + (bc + (a + b)) =
  -- ac + ((bc + a) + b) = ac + ((a + bc) + b) = (ac + (a+bc)) + b =
  -- ((ac + a) + bc) + b = (aS(c) + bc) + b = aS(c) + (bc + b) = aS(c) + bS(c)


def mult_associative (a b c : myN) : ((a × b) × c) ≡ (a × (b × c)) :=
  match c with
  | myN.one => (mult_one_right _)
  | myN.succ c' =>
  -- (ab)c = (ab)c' + ab = a(bc')+ab = a(bc'+b) = a(bc)
    mult_successor_right _ _ •
    ap (myAdd_right (a × b)) ((a × b) × c') (a × (b × c')) (mult_associative _ _ _) •
    myEq_symm (mult_distributive_left _ _ _) •
    ap (myMult a) ((b × c') + b) (b × c'.succ) (myEq_symm (mult_successor_right _ _))

end Naturals

namespace Integers
open chapter3_naturals
open chapter3_integers
open chapter5_myeq
open chapter4_integers


def right_equiv_add (x : myZ) (p : a ≡ b) : myAdd x a ≡ myAdd x b :=
  ap (fun y => (myAdd x y)) a b p

def left_equiv_add (x : myZ) (p : a ≡ b) : myAdd a x ≡ myAdd b x :=
  ap (fun y => (myAdd y x)) a b p


-- Exercise 5.6

def succ_pred_elim (k : myZ) : succZ (predZ k) ≡ k :=
  match k with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl (myN.succ _)) => MyEq.refl _
  | Sum.inr (Sum.inl myN.one) => MyEq.refl _
  | Sum.inl (myN.succ _) => MyEq.refl _
  | Sum.inl (myN.one) => MyEq.refl _

def pred_succ_elim (k : myZ) : predZ (succZ k) ≡ k :=
  match k with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl (myN.succ _)) => MyEq.refl _
  | Sum.inr (Sum.inl myN.one) => MyEq.refl _
  | Sum.inl (myN.succ _) => MyEq.refl _
  | Sum.inl (myN.one) => MyEq.refl _

def pred_succ_symm (z : myZ) := pred_succ_elim z • myEq_symm (succ_pred_elim z)
def succ_pred_symm (z : myZ) := succ_pred_elim z • myEq_symm (pred_succ_elim z)

-- Exercise 5.7
-- a)

def left_add_zero_toZpos (n : myN) : addNaturalToZ n Zzero ≡ Zpos n :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap succZ _ _ (left_add_zero_toZpos n')

def left_add_zero_toZneg (n : myN) : subtractNaturalFromZ n Zzero ≡ Zneg n :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (left_add_zero_toZneg n')


def left_add_zero (x : myZ) : (myAdd Zzero x) ≡ x :=
  match x with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl x') => left_add_zero_toZpos x'
  | Sum.inl x' => left_add_zero_toZneg x'

def right_add_zero (x : myZ) : (myAdd x Zzero) ≡ x := MyEq.refl _


-- b)

def addNtoZ_left_pred_law (n: myN) (z : myZ) : addNaturalToZ n (predZ z) ≡ predZ (addNaturalToZ n z) :=
  match n with
  | myN.one => succ_pred_symm z
  | myN.succ n' => by
    have h : succZ (addNaturalToZ n' (predZ z)) ≡ succZ (predZ (addNaturalToZ n' z)) :=
      ap succZ _ _ (addNtoZ_left_pred_law n' z)
    exact h • myEq_symm (pred_succ_symm (addNaturalToZ n' z))

def subNfromZ_left_pred_law (n: myN) (z : myZ) : subtractNaturalFromZ n (predZ z) ≡ predZ (subtractNaturalFromZ n z) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (subNfromZ_left_pred_law n' z)


def addNtoZ_left_succ_law (n: myN) (z : myZ) : addNaturalToZ n (succZ z) ≡ succZ (addNaturalToZ n z) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => by
    have h : succZ (addNaturalToZ n' (succZ z)) ≡ succZ (succZ (addNaturalToZ n' z)) :=
      ap succZ _ _ (addNtoZ_left_succ_law n' z)
    exact h

def subNfromZ_left_succ_law (n: myN) (z : myZ) : subtractNaturalFromZ n (succZ z) ≡ succZ (subtractNaturalFromZ n z) :=
  match n with
  | myN.one => pred_succ_symm z
  | myN.succ n' => ap predZ _ _ (subNfromZ_left_succ_law n' z) • (pred_succ_symm (subtractNaturalFromZ n' z))




def left_pred_law (x y : myZ) : myAdd (predZ x) y ≡ predZ (myAdd x y) :=
  match y with
  | Sum.inr (Sum.inr _) => (right_add_zero (predZ x)) • (myEq_symm (ap predZ (myAdd x Zzero) x (right_add_zero x)))
  | Sum.inl y' => subNfromZ_left_pred_law y' x
  | Sum.inr (Sum.inl y') => addNtoZ_left_pred_law y' x

def right_pred_law (x y : myZ) : myAdd x (predZ y) ≡ predZ (myAdd x y) :=
  match y with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inl _ => MyEq.refl _
  | Sum.inr (Sum.inl myN.one) => myEq_symm (pred_succ_elim x)
  | Sum.inr (Sum.inl (myN.succ n)) => myEq_symm (pred_succ_elim (myAdd x (Sum.inr (Sum.inl n))))


def right_succ_law (x y : myZ) : myAdd x (succZ y) ≡ succZ (myAdd x y) :=
  match y with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl _) => MyEq.refl _
  | Sum.inl myN.one => myEq_symm (succ_pred_elim x)
  | Sum.inl (myN.succ n) => myEq_symm (succ_pred_elim (myAdd x (Sum.inl n)))

def left_succ_law (x y : myZ) : myAdd (succZ x) y ≡ succZ (myAdd x y) :=
  match y with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl n) => addNtoZ_left_succ_law n x
  | Sum.inl n => subNfromZ_left_succ_law n x


-- c)

def addNtoZ_associative (n : myN) (x y : myZ) : addNaturalToZ n (myAdd x y) ≡ myAdd x (addNaturalToZ n y) :=
  match n with
  | myN.one => myEq_symm (right_succ_law x y)
  | myN.succ n' => (ap succZ _ _ (addNtoZ_associative n' x y)) • myEq_symm (right_succ_law x (addNaturalToZ n' y))

def subNfromZ_associative (n : myN) (x y : myZ) : subtractNaturalFromZ n (myAdd x y) ≡ myAdd x (subtractNaturalFromZ n y) :=
  match n with
  | myN.one => myEq_symm (right_pred_law x y)
  | myN.succ n' => (ap predZ _ _ (subNfromZ_associative n' x y)) • myEq_symm (right_pred_law x (subtractNaturalFromZ n' y))

def addZ_associative (x y z : myZ) : myAdd (myAdd x y) z ≡ myAdd x (myAdd y z) :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => addNtoZ_associative z' x y
  | Sum.inl z' => subNfromZ_associative z' x y


def left_add_one_toZpos (n : myN) :  myAdd (Sum.inr (Sum.inl myN.one)) (Sum.inr (Sum.inl n)) ≡ succZ (Sum.inr (Sum.inl n)) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap succZ _ _ (left_add_one_toZpos n')

def left_add_one_toZneg (n : myN) :  myAdd (Sum.inr (Sum.inl myN.one)) (Sum.inl n) ≡ succZ (Sum.inl n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (left_add_one_toZneg n') • pred_succ_symm (Sum.inl n')

def left_sub_one_toZpos (n : myN) :  myAdd (Sum.inl myN.one) (Sum.inr (Sum.inl n)) ≡ predZ (Sum.inr (Sum.inl n)) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap succZ _ _ (left_sub_one_toZpos n') • succ_pred_symm (Sum.inr (Sum.inl n'))

def left_sub_one_toZneg (n : myN) :  myAdd (Sum.inl myN.one) (Sum.inl n) ≡ predZ (Sum.inl n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => ap predZ _ _ (left_sub_one_toZneg n')

def left_add_one (z : myZ) : myAdd (Sum.inr (Sum.inl myN.one)) z ≡ succZ z :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => left_add_one_toZpos z'
  | Sum.inl z' => left_add_one_toZneg z'

def left_sub_one (z : myZ) : myAdd (Sum.inl myN.one) z ≡ predZ z :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => left_sub_one_toZpos z'
  | Sum.inl z' => left_sub_one_toZneg z'

def addNtoZ_commutative (n : myN) (z : myZ) : addNaturalToZ n z ≡ myAdd (Sum.inr (Sum.inl n)) z :=
  match n with
  | myN.one => myEq_symm (left_add_one z)
  | myN.succ n' => ap succZ _ _ (addNtoZ_commutative n' z) • myEq_symm (left_succ_law (Sum.inr (Sum.inl n')) z)

def subNfromZ_commutative (n : myN) (z : myZ) : subtractNaturalFromZ n z ≡ myAdd (Sum.inl n) z :=
  match n with
  | myN.one => myEq_symm (left_sub_one z)
  | myN.succ n' =>  ap predZ _ _ (subNfromZ_commutative n' z) • myEq_symm (left_pred_law (Sum.inl n') z)

def addZ_commutative (x y : myZ) : myAdd x y ≡ myAdd y x :=
  match y with
  | Sum.inr (Sum.inr _) => (right_add_zero x) • myEq_symm (left_add_zero x)
  | Sum.inr (Sum.inl y') => addNtoZ_commutative y' x
  | Sum.inl y' => subNfromZ_commutative y' x


-- d)

def addNtoZ_inverse (n : myN) : addNaturalToZ n (Sum.inl n) ≡ Zzero :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
    (addNtoZ_left_pred_law n'.succ (Sum.inl n')) •
    (pred_succ_elim (addNaturalToZ n' (Sum.inl n'))) •
    (addNtoZ_inverse n')

def subNfromZ_inverse (n : myN) : subtractNaturalFromZ n (Sum.inr (Sum.inl n)) ≡ Zzero :=
  match n with
  | myN.one => MyEq.refl _(
  | myN.succ n' =>
    (subNfromZ_left_succ_law n'.succ (Sum.inr (Sum.inl n'))) •
    (succ_pred_elim (subtractNaturalFromZ n' (Sum.inr (Sum.inl n')))) •
    (subNfromZ_inverse n')



def left_inverse_law (z : myZ) : myAdd (negative z) z ≡ Zzero :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => addNtoZ_inverse z'
  | Sum.inl z' => subNfromZ_inverse z'

def right_inverse_law (z : myZ) : myAdd z (negative z) ≡ Zzero :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => subNfromZ_inverse z'
  | Sum.inl z' => addNtoZ_inverse z'


--Exercise 5.8

-- a)

def multNatWithZero (n : myN) : multNaturalWithZ Zzero n ≡ Zzero :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' => left_add_zero (multNaturalWithZ Zzero n') • (multNatWithZero n')

def multNatWithOne (n : myN) : multNaturalWithZ (Sum.inr (Sum.inl myN.one)) n ≡ Sum.inr (Sum.inl n) :=
  match n with
  | myN.one => MyEq.refl _
  | myN.succ n' =>
  left_add_one (multNaturalWithZ (Sum.inr (Sum.inl myN.one)) n') •
  (ap succZ _ _ (multNatWithOne n'))

def right_multby0 (z : myZ) : myMult z Zzero ≡ Zzero := MyEq.refl _

def left_multby0 (z : myZ) : myMult Zzero z ≡ Zzero :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => multNatWithZero z'
  | Sum.inl z' => ap negative _ _ (multNatWithZero z')

def right_multbyOne (z : myZ) : myMult z (Sum.inr (Sum.inl myN.one)) ≡ z := MyEq.refl _

def left_multbyOne (z : myZ) : myMult (Sum.inr (Sum.inl myN.one)) z ≡ z :=
  match z with
  | Sum.inr (Sum.inr _) => MyEq.refl _
  | Sum.inr (Sum.inl z') => multNatWithOne z'
  | Sum.inl z' => ap negative _ _ (multNatWithOne z')

end Integers
