import Std.Data.HashMap.Basic
import Mathlib.Data.List.Monad
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Set.Defs

#check Functor

-- List is a Functor
#check List.instFunctor
-- So we can use `map` with a List
#check List.map
#eval [1,2,3].map (λ x => x + 1)

-- Option is a Functor
#check Option.map
#eval (none).map (λ x : ℕ => x + 1)
#eval (some 1).map (λ x => x + 1)

--
#eval (do
  IO.println "test"
  IO.println "note"
  )

#check Applicative


#check Monad
#check List.instMonad

def whatList : List ℕ := do
  let a ← [2,3,5]
  let b ← [2,4,8]
  pure (a ^ b)
#eval whatList

-- StateT is a Monad
#check StateT.instMonad

def sum (xs : List ℕ) : ℕ := Id.run <| do
  let mut res := 0
  for x in xs do
    res := res + x
  return res
#eval sum [1,2,3]

def getEvenOdd (xs : List ℕ) : IO Unit := do
  let mut evens := #[]
  let mut odds := #[]
  for x in xs do
    if x % 2 == 0 then
      evens := evens.push x
    else
      odds := odds.push x
  IO.println s!"evens: {evens} odds:{odds}"
#eval getEvenOdd [1,2,3]

open Std

structure State (s α : Type) where
  run : s → α × s

namespace State
def get : State S S := ⟨λ s ↦ (s,s)⟩
def update (f : S → S) : State S Unit := ⟨λ s ↦ ((),f s)⟩
def run'[Inhabited S](x : State S α) (s : S := default) : α := (x.run s).1
end State

instance : Monad (State S) where
  pure x := ⟨λ s ↦ (x,s)⟩
  bind x f := ⟨λ s ↦ let (a,s') := x.run s; (f a).run s'⟩

instance [rep : Repr α][Inhabited S] : Repr (State S α) :=
  ⟨λ mx n ↦ rep.reprPrec mx.run' n⟩

-- State Monad for mutability
def fibM (n : ℕ) : State (HashMap ℕ ℕ) ℕ := do
  let s ← State.get
  if let some y := s[n]? then
    return y
  match n with
  | 0 => return 1
  | 1 => return 1
  | k + 2 => do
    let f₁ ← fibM k
    let f₂ ← fibM (k + 1)
    let sum := f₁ + f₂
    State.update λ m ↦ m.insert n sum
    return sum

#eval fibM 13
