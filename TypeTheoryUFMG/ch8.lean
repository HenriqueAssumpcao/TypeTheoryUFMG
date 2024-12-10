-- Chapter 8

-- Exercises

namespace c8ex6

def greater (x y : Int) := x > y

def eqv (k l m : Int) (u: greater m 0) := ∃x:Int, k-l = x*m 

variable (u : greater 5 0)

def p1 := eqv (-3) 17 5 u

def p2 := ¬(eqv (-3) (-17) 5 u)

def refl_eqv (k l m :Int) (u: greater m 0) := eqv k l m u -> eqv l k m u

def iff_eqv (k l m :Int) (u: greater m 0) := eqv k l m u ↔ ∃x:Int,k = l + x*m 

end c8ex6
