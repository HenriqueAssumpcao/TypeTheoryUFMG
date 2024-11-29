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


