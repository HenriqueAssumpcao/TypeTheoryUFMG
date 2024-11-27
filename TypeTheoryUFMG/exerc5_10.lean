def ex5_12
  (S : Type)
  (R : S → S → Type)
  (u : (x y : S) → R x y → R y x)
  (v : (x y z : S) → R x y → R x z → R y z)
  : (x y : S) → R x y → R x x :=
  fun x y hipotese =>
  let k : R y x := u x y hipotese
  let l : R x x := v y x x k k
  l

theorem ex5_12p
  (S : Prop)
  (R : S → S → Prop)
  (u : (x y : S) → R x y → R y x)
  (v : (x y z : S) → R x y → R x z → R y z)
  : (x y : S) → R x y → R x x :=  by
  intro x y hipotese
  apply v
  repeat {
    apply u
    exact hipotese
  }

  theorem ex5_10  
    (S : Prop)
    (P : S → Prop)
    (f : S → S)
    (g : S → S)
    (u : (x : S) → P (f x) → P (g x))
    (v : (x y : S) → (P x → P y) → P (f x)) : 
    (x : S) → P (f (f x)) :=  by 
    intro (x : S) 
    exact v (f x) (g x) (u x)   
    

    
