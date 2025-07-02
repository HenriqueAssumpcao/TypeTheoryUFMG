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


--attribute [instance] WellOrder.wo
--Isso registra o campo wo como uma instância typeclass.
--Isso significa que sempre que Lean precisar encontrar uma prova de IsWellOrder α r
--para um WellOrder específico ele saberá onde procurar.


lemma emptyiswellorder : IsWellOrder PEmpty EmptyRelation :=
   inferInstance

instance : Inhabited WellOrder where
  default := WellOrder.mk
             PEmpty EmptyRelation
             emptyiswellorder



#check Setoid WellOrder
#check Nonempty
#check RelIso.symm

#check Nonempty ℕ

def emptywellorder : WellOrder :=
  WellOrder.mk PEmpty EmptyRelation emptyiswellorder

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. --/

instance Ordinal.isEquivalent : Setoid WellOrder where
  r := fun WO1 WO2 => Nonempty (RelIso WO1.r WO2.r)
  -- iseqv := Equivalence.mk (fun (WellOrder α r wo) => RelIso.refl r) (sorry) (sorry)
  iseqv :=  Equivalence.mk
     (fun WO =>  ⟨RelIso.refl WO.r⟩)
     (fun ⟨e⟩ =>  ⟨RelIso.symm  e⟩)
     (fun ⟨e₁⟩ ⟨e₂⟩ => ⟨RelIso.trans e₁ e₂⟩)


/-- `Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/

def Ordinal : Type (u + 1) :=
  Quotient Ordinal.isEquivalent

