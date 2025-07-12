variable (α β γ : Prop)
variable (A B C : Prop)

/-
   Exercises for chapter 2 of the book 'Type Theory and Formal Proof' by
   Rob Nederpelt, Herman Geuvers, and Fredrik de Vries.
-/

/- Exercise 2.1
   Investigate for each of the following λ-terms whether they can be typed
   with a simple type. If so, give a type for the term and the corresponding
   types for x and y. If not, explain why.
   (a) x x y,
   (b) x y y,
   (c) x y x,
   (d) x(x y),
   (e) x(y x)
-/

-- solution for (a)
-- The term in item (a) cannot be typed with a simple type since it
-- contains an application of x to itself.

-- solution for (b)
example (x : α → (α → β)) (y : α) : β :=
  (x y) y -- this is well-typed, with x of type α → (α → β) and y of type α

-- solution for (c)
/-
Suppose that x y x has type σ. So exists type α such that (x : α) and (x y : α → σ)
But (x y : α → σ) implies that exists type β such that (x : β → α → σ) and (y : β)
So α ≡ β → α → σ but that is impossible.
-/

-- solution for (d)
example (x : α → α) (y : α) : α :=
  x (x y) -- This is well-typed, with x of type α → α and y of type α

-- solution for (e)
example (x : α → β) (y : (α → β) → α) : β :=
  x (y x) -- this is well-typed, with x of type α → β and y of type (α → β) → α

-- ##################################


/- Exercise 2.4
Add types to the bound variables in the following λ-terms such that they
become pre-typed λ-terms which are legal, and give their types:
  (a) λxyz. x(yz),
  (b) λxyz. y(xz)x
-/

-- solution for (a)

def term_2_4_a := λ (x : β → α) (y : γ → β) (z : γ) => x (y z)
-- When hovering the cursor over the λ-term his type is showed.
-- We conclude that this term is legal with context Γ ≡ ∅

-- solution for (b)

def term_2_4_b := fun (x : α → β) (y : β → (α → β) → γ) (z : α) => y (x z) x
-- Here we uses "fun" instead of "λ". Just to show that's work too.

-- ###########################################


/- Exercise 2.5
For each of the following terms, try to find a pre-typed variant which is
typable. If this is not possible, show why.
  (a) λxy. x(λz. y)y,
  (b) λxy. x(λz. x)y.
-/

-- solution for (a)

def term_2_5_a := λ(x : (α → β) → β → γ) (y : β) => x (λ (_ : α) => y) y
-- Here "z" was replaced to "_" to avoid the annoying alert signal.

-- solution for (b)

/-
This term isn't typable because if (z : α) and (x : β) so (λz. x : α → β)
and that's make impossible to apply x(λz. x)
-/

-- #################################################


/-Exercise 2.7
  (a) Prove the following by giving a kind of derivation, with the rules
    (func-appl) and (func-abst) described in Example 2.4.8:
    If (f : A → B) and (g : B → C), then (g◦f : A → C).
    (Note: g◦f is the composition of f and g, being the function mapping x to g(fx).)

  (b) Give a derivation in natural deduction of the following expression,
    using the rules ⇒-elim and ⇒-intro described in Example 2.4.9:
    (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)).

  (c) Prove that the following pre-typed λ-term is legal, using the flag for
    mat:
    λz : α.y(xz).

  (d) Indicate the similarities between the derivations in (a), (b) and (c).
-/

-- solution for (a)

example (f : A → B) (g : B → C) : A → C :=
  λ (x : A) => g (f x)

-- solution for (b)

example : (A → B) → ((B → C) → (A → C)) := by
  intro h1          -- Assume : A → B
  intro h2          -- Assume : B → C
  intro h3          -- Assume : A
  have h4 := h1 h3  -- Using (=>-elim) on h1 h3
  have h5 := h2 h4  -- Using (=>-elim) on h2 h4
  exact h5

  -- Assuming that h1, h2 and h3 holds we showed that h5 holds
  -- Thus, using (=>-intro) 3 times we have (A → B) → ((B → C) → (A → C))

-- "solution" for (b) on a shorter way

example  : (A → B) → ((B → C) → (A → C)) := by
  intro h1 h2 h3
  exact h2 (h1 h3)

-- solution for (c)
  -- Sorry

-- solution for (d)
  --Sorry

--###################################################


/- Exercise 2.8
  (a) Add types to the bound variables in the λ-term λxy. y(λz. yx) such
    that the type of this term becomes
    (γ → β) → ((γ → β) → β) → β.
  (b) Give a derivation in tree format, proving this.
  (c) Sketch a diagram of the tree structure, as in Section 2.5.
  (d) Transform the derivation into flag format.
-/

-- solution for (a)

example : (γ → β) → ((γ → β) → β) → β :=
  λ (x : γ → β) (y : (γ → β) → β) => y (λ (_ : γ) => y x)

-- So (x : γ → β), (y : (γ → β) → β) and (z : γ) satisfies.

-- solution for (b)
  -- Sorry
-- solution for (c)
  -- Sorry
-- solution for (d)
  -- Sorry

-- #####################################################


/-Exercise 2.9
Give derivations by means of which the following judgements become type-checked.
You may use the flag notation. In part (b), you may use flag notation in its ‘shortened’ form,
i.e. suppress steps involving the (var)-rule.
  (a) x : δ → δ → α, y : γ → α, z : α → β
        λu : δ. λv : γ. z(yv) : δ → γ → β,
  (b) x : δ → δ → α, y : γ → α, z : α → β
        λu : δ. λv : γ. z(xuu) : δ → γ → β.
-/

-- "solution" for (a)

def term_2_9_a (_ : δ → δ → α) (y : γ → α) (z : α → β) := λ (_ : δ) (v : γ) => z (y v)
-- We can see that his type is δ → γ → β exactly how was required.

-- "solution" for (b)
def term_2_9_b (x : δ → δ → α) (_ : γ → α) (z : α → β) := λ (u : δ) (_ : γ) => z (x u u)
-- We can see that his type is δ → γ → β exactly how was required.

-- ######################################################


/-Exercise 2.10
Prove that the following pre-typed λ-terms are legal, by giving derivations
in (shortened) flag notation.
  (a) xz(yz),
  (b) λx : (α → β) → β. x(yz),
  (c) λy : α. λz : β → γ. z(xyy),
  (d) λx : α → β. y(xz)z.
-/

-- solution for (a)

def term_2_10_a (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

-- solution for (b)

def term_2_10_b (y : α → α → β) (z : α) := λ(x : (α → β) → β) => x (y z)

-- solution for (c)

def term_2_10_c (x : α → α → β) := λ(y : α) => λ(z : β → γ) => z (x y y)

-- solution for (d)

def term_2_10_d (y : β → α → γ) (z : α) := λ(x : α → β) => y (x z) z

-- ##########################################################


/-
   Exercise 2.11. Find inhabitants of the following types in the empty context, by giving
   appropriate derivations.

   (a) (α → α → γ) → α → β → γ
   (b) (α → γ) → α) → (α → γ) → β → γ
-/

-- solution for part (a)
example (g : (α → γ) → α) : (α → γ) → ( β → γ ) :=
  fun (a : α → γ) => fun (_ : β) => a (g a)


-- solution for part (b)
example : ((α → γ) → α) → (α → γ) → (β → γ) :=
  fun (g : (α → γ) → α) =>  (fun (a : α → γ) => fun (_ : β) => a (g a))

-- ################################


/- Exercise 2.12
(a) Construct a term of type ((α → β) → α) → ((α → (α → β)) → α)
(b) Construct a term of type ((α → β) → α) → (α → α → β) → β. Hint: use (a).
-/

-- solution for (a)

example : ((α → β) → α) → ((α → (α → β)) → α) :=
  fun (g : (α → β) → α) =>
    fun (h : α → (α → β)) =>
      g (fun a : α => (h a) a) -- this is the term of type (α → β) that g expects

-- second solution for (a) as a theorem

theorem part_a {α β : Prop} : ((α → β) → α) → ((α → (α → β)) → α) := by
  intro h
  intro g

  have  t : α → β := by
    intro a
    exact g a a

  exact h t

-- solution for (b) using (a)

example : ((α → β) → α) → (α → α → β) → β := by
   intro h
   intro g
   exact g (part_a h g) (part_a h g)

-- ####################################################


/- Exercise 2.13
Find a term of type τ in context Γ, with:
  (a) τ ≡ (α → β) → α → γ, Γ ≡ x : α → β → γ,
  (b) τ ≡ α → (α → β) → γ, Γ ≡ x : α → β → α → γ,
  (c) τ ≡ (α → γ) → (β → α) → γ, Γ ≡ x : (β → γ) → γ.
-/

-- Solution for (a)

example (x : α → β → γ) : (α → β) → α → γ := by
  intro g
  intro a
  exact x a (g a)

-- Solution for (b)

example (x : α → β → α → γ) : α → (α → β) → γ := by
  intro a
  intro g
  exact x a (g a) a

-- Solution for (c)

example (x : (β → γ) → γ) : (α → γ) → (β → α) → γ := by
  intro g
  intro h
  have f := fun b : β => g (h b)

  exact x f

-- ######################################################


/- Exercise 2.14
Find an inhabitant of the type α → β → γ in the following context:
  Γ ≡ x : (γ → β) → α → γ.
-/

example (x : (γ → β) → α → γ) : α → β → γ := by
  intro a
  intro b
  have g := fun _ : γ => b

  exact x g a
