-- Code by Csaba

variable( A B : Prop )

/- Exercice 7.7 of Nederpelt and Geuvers
   Prove the ∨-left-sec and ∨-intro-right-sec rules.

  The ∨-left-sec rule says that proposition A implies
  Π C:* . (A → C) → (B → C) → C

  The ∨-right-sec rule says that proposition B implies
  Π C:* . (A → C) → (B → C) → C

  That is, Π C:* . (A → C) → (B → C) → C can be viewed as a
  λC-implementation of the logical **OR**.
-/

-- Proving ∨-left-sec
-- the first solution is given by constructing a function directly

example(x : A) : ∀C : Prop, (A → C) → (B → C) → C :=
  fun C : Prop =>
    fun z : A → C =>
    fun _ : B → C => z x

-- the second solution is using tactics

example (x : A) : ∀C : Prop, (A → C) → (B → C) → C := by
  intro       -- introduces C : Prop;  goal now (A → C) → (B → C) → C
  intro z     -- introduces z : A → C; goal now (B → C) → C
  intro       -- introduces _ : B → C; goal now C
  exact z x   -- this has type C

-- Proving ∨-right-sec
-- the first solution is given by constructing a function directly

example(y : B) : ∀C : Prop, (A → C) → (B → C) → C :=
  fun C : Prop =>
    fun _ : A → C =>
    fun u : B → C => u y

-- the second solution is using tactics

example (y : B) : ∀C : Prop, (A → C) → (B → C) → C := by
  intro       -- introduces C : Prop;  goal now (A → C) → (B → C) → C
  intro       -- introduces _ : A → C; goal now (B → C) → C
  intro u     -- introduces u : B → C; goal now C
  exact u y   -- this has type C


/-
  To complete the investigation of ∨, let us prove the ∨-elim-sec on page 143
  of Nederpelt and Geuvers.

  Thus rule says that if Π D:* . (A → D) → (B → D) → D, A → C, B → C, then C.
-/

-- first, direct proof

example (x : ∀D : Prop, (A → D) → (B → D) → D) (y : A → C) (z : B → C) : C :=
  x C y z

-- now, the proof using tactic

example (x : ∀D : Prop, (A → D) → (B → D) → D) (y : A → C) (z : B → C) : C := by
  exact x C y z

