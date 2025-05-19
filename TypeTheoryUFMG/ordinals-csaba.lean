import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Sum.Order
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.PPWithUniv

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.
-/

assert_not_exists Module
assert_not_exists Field
noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Definition of ordinals -/

structure WellOrder : Type (u + 1) where              --estrutura que vive no universo Type (u + 1)
  /-- The underlying type of the order. -/
  α : Type u                                          --O tipo abaixo que está sendo ordenado
  /-- The underlying relation of the order. -/
  r : α → α → Prop                                    -- A relação de ordem
  /-- The proposition that `r` is a well-ordering for `α`. -/
  wo : IsWellOrder α r                          -- A propriedade de que a relação é uma ordem total


lemma emptyiswellorder : IsWellOrder PEmpty EmptyRelation :=
   inferInstance


instance : Inhabited WellOrder where
  default := WellOrder.mk
             PEmpty EmptyRelation
             emptyiswellorder


def emptywellorder : WellOrder :=
  WellOrder.mk PEmpty EmptyRelation emptyiswellorder

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. --/

instance Ordinal.isEquivalent : Setoid WellOrder where
  r := fun WO1 WO2 => Nonempty (RelIso WO1.r WO2.r)
  -- iseqv := Equivalence.mk (fun (WellOrder α r wo) => RelIso.refl r) (sorry) (sorry)
  iseqv :=  Equivalence.mk
    (fun (wo : WellOrder) => Nonempty.intro (RelIso.refl wo.r))
    (fun {wo₁ wo₂ : WellOrder} (h: Nonempty (wo₁.r ≃r wo₂.r)) =>
        h.map RelIso.symm)
        -- h.map :  (α → β) →  (Nonempty α → Nonempty β)
        -- RelIso.symm :  (r ≃r s) →  s ≃r r
    (fun {wo₁ wo₂ wo₃: WellOrder}
         (h₁ : Nonempty (wo₁.r ≃r wo₂.r))
         (h₂  : Nonempty (wo₂.r ≃r wo₃.r)) =>
        Nonempty.elim h₁ (fun (e₁ : wo₁.r ≃r wo₂.r) =>
          h₂.map (fun (e₂ : wo₂.r ≃r wo₃.r) =>
          RelIso.trans e₁ e₂)))
       -- Nonempty.elim (Nonempty α) → (α → p) → p
       -- RelIso.trans (r ≃r s) → (s ≃r t) →  (r ≃r t)
       -- function in argument : (wo₁.r ≃r wo₂.r) → (wo₂.r ≃r wo₃.r) →  (wo₁.r ≃r wo₃.r)
       -- h₂.map :  (α → β) →  (Nonempty α → Nonempty β)


/-- `Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/

def Ordinal : Type (u + 1) :=
  Quotient  Ordinal.isEquivalent

-- Use this over `Iio o` only when it is paramount to have a `Type u` rather than a `Type (u + 1)`. -/

def Ordinal.toType (o : Ordinal.{u}) : Type u :=
  -- Choose an element of the equivalence class using the axiom of choice.
  -- Sound but noncomputable.
  -- return the type of the chosen element
  o.out.α

instance hasWellFounded_toType (o : Ordinal) : WellFoundedRelation o.toType :=
  WellFoundedRelation.mk o.out.r o.out.wo.wf

namespace Ordinal
/-- The ordinal corresponding to a given well order. -/

def ofWellOrder (wo : WellOrder) : Ordinal :=
  Quotient.mk Ordinal.isEquivalent wo
/-! ### Basic properties of the order type -/

/-- The order type of a well order is an ordinal. -/
def type {α : Type u} (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  Quotient.mk Ordinal.isEquivalent (WellOrder.mk α r wo)

instance zero : Zero Ordinal :=
  Zero.mk (Quotient.mk Ordinal.isEquivalent emptywellorder)

#check (0 : Ordinal)

instance inhabited : Inhabited Ordinal :=
  Inhabited.mk 0

lemma one_is_well_order : IsWellOrder PUnit (@EmptyRelation PUnit):=
  inferInstance

def one_ordinal : Ordinal :=
  Quotient.mk Ordinal.isEquivalent
    (WellOrder.mk  PUnit (@EmptyRelation PUnit) one_is_well_order)

instance one : One Ordinal :=
  One.mk one_ordinal


theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop}
                      [IsWellOrder α r] [IsWellOrder β s] :
                      type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'

theorem _root_.RelIso.ordinal_type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩

theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinal_type_eq
