/-
  Chapter 9 — Exercises 9.1–9.9 (Rijke, December 2022 edition).
  Proof-relevant identities, explicit inverses and homotopies, as in chapter9.
  The universe is Type 0, following the existing MyEq and myProd definitions.
-/
import HoTTRijke.chapter9
import HoTTRijke.chapter8_exercises

open chapter5_myeq chapter3_booleans chapter3_naturals_with_zero

namespace chapter9

/- Exercise 9.1: inversion, concatenation, and transport. -/
def equiv_path_inv {A : Type} (x y : A) : equiv (x ≡ y) (y ≡ x) :=
  equiv_of_inverse myEq_symm myEq_symm
    (fun p => by cases p; exact MyEq.refl _)
    (fun p => by cases p; exact MyEq.refl _)

def equiv_concat_left {A : Type} {x y : A} (p : x ≡ y) (z : A) :
    equiv (y ≡ z) (x ≡ z) := by
  refine equiv_of_inverse (concat_eq p) (concat_eq (myEq_symm p)) ?_ ?_
  · intro q; cases p; exact MyEq.refl _
  · intro q; cases p; exact MyEq.refl _

def equiv_concat_right {A : Type} (x : A) {y z : A} (q : y ≡ z) :
    equiv (x ≡ y) (x ≡ z) := by
  refine equiv_of_inverse (fun p => p • q) (fun p => p • myEq_symm q) ?_ ?_
  · intro p; cases q; cases p; exact MyEq.refl _
  · intro p; cases q; cases p; exact MyEq.refl _

def equiv_transport {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) :
    equiv (B x) (B y) := by
  refine equiv_of_inverse (transport B p) (transport B (myEq_symm p)) ?_ ?_
  · intro b; cases p; exact MyEq.refl _
  · intro b; cases p; exact MyEq.refl _

/- Exercise 9.2: examples of types and maps that are not equivalent. -/
def not_is_equiv_const_bool (b : myBool) : myNegType (is_equiv (fun _ : myBool => b)) :=
  fun E =>
    let s := proj1 E
    chapter6_Universes.neg_injective b
      (chapter6_Universes.Eq_bool_equiv_conv b (myNeg b) (s.2 (myNeg b)))

def not_equiv_bool_unit : myNegType (equiv myBool Unit) := by
  intro e
  let r := proj2 e.2
  have same (u v : Unit) : u ≡ v := by cases u; cases v; exact MyEq.refl _
  exact chapter6_Universes.neg_injective myBool.myTrue
    (chapter6_Universes.Eq_bool_equiv_conv _ _
      (myEq_symm (r.2 myBool.myTrue) •
        ap r.1 _ _ (same (e.1 myBool.myTrue) (e.1 myBool.myFalse)) • r.2 myBool.myFalse))

-- Every natural-valued function on a finite type has a computable bound.
def bound_fin : (k : myN) → (myFin k → myN) → myN
  | myN.zero, _ => myN.zero
  | myN.succ k, f => myAdd (bound_fin k (fun x => f (Sum.inl x))) (f (Sum.inr ()))

def leq_bound_fin : (k : myN) → (f : myFin k → myN) → (x : myFin k) →
    chapter8.leq (f x) (bound_fin k f)
  | myN.zero, _, e => nomatch e
  | myN.succ k, f, Sum.inl x => chapter8.leq_trans _ _ _
      (leq_bound_fin k (fun y => f (Sum.inl y)) x) (chapter8.leq_add_right _ _)
  | myN.succ _, _, Sum.inr () => chapter8.leq_add_left _ _

def not_equiv_naturals_fin (k : myN) : myNegType (equiv myN (myFin k)) := by
  intro e
  let r := proj2 e.2
  let n := bound_fin k r.1
  have h := leq_bound_fin k r.1 (e.1 n.succ)
  exact chapter8.not_leq_succ_self n (transport (fun t => chapter8.leq t n) (r.2 n.succ) h)

/- Exercise 9.3: invariance under homotopy. -/
def is_equiv_of_htpy {A B : Type} {f g : A → B} (H : htpy f g)
    (E : is_equiv f) : is_equiv g :=
  myProd.mk
    ⟨(proj1 E).1, fun y => myEq_symm (H ((proj1 E).1 y)) • (proj1 E).2 y⟩
    ⟨(proj2 E).1, fun x => ap (proj2 E).1 _ _ (myEq_symm (H x)) • (proj2 E).2 x⟩

def is_equiv_iff_htpy {A B : Type} {f g : A → B} (H : htpy f g) :
    myEquiv (is_equiv f) (is_equiv g) :=
  myProd.mk (is_equiv_of_htpy H) (is_equiv_of_htpy (inv_htpy H))

def htpy_inv_equiv {A B : Type} (e e' : equiv A B) (H : htpy e.1 e'.1) :
    htpy (inv_equiv e) (inv_equiv e') :=
  let I := has_inverse_of_is_equiv e'.2
  fun y => myEq_symm (proj2 I.2 (inv_equiv e y)) •
    ap I.1 _ _ (myEq_symm (H (inv_equiv e y)) • (proj1 e.2).2 y)

/- Exercise 9.4: commuting triangles and the 3-for-2 property. -/
def triangle_sec {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (s : sec h) : htpy g (f ∘ s.1) :=
  fun b => myEq_symm (ap g _ _ (s.2 b)) • myEq_symm (H (s.1 b))

def sec_iff_triangle {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (s : sec h) : myEquiv (sec f) (sec g) :=
  myProd.mk
    (fun t => ⟨h ∘ t.1, fun x => myEq_symm (H (t.1 x)) • t.2 x⟩)
    (fun t => ⟨s.1 ∘ t.1, fun x => myEq_symm (triangle_sec H s (t.1 x)) • t.2 x⟩)

def triangle_retr {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (r : retr g) : htpy h (r.1 ∘ f) :=
  fun a => myEq_symm (r.2 (h a)) • ap r.1 _ _ (myEq_symm (H a))

def retr_iff_triangle {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (r : retr g) : myEquiv (retr f) (retr h) :=
  myProd.mk
    (fun t => ⟨t.1 ∘ g, fun a => ap t.1 _ _ (myEq_symm (H a)) • t.2 a⟩)
    (fun t => ⟨t.1 ∘ r.1, fun a =>
      ap t.1 _ _ (myEq_symm (triangle_retr H r a)) • t.2 a⟩)

def is_equiv_comp {A B C : Type} {f : A → B} {g : B → C}
    (F : is_equiv f) (G : is_equiv g) : is_equiv (g ∘ f) :=
  myProd.mk
    ⟨(proj1 F).1 ∘ (proj1 G).1, fun c =>
      ap g _ _ ((proj1 F).2 ((proj1 G).1 c)) • (proj1 G).2 c⟩
    ⟨(proj2 F).1 ∘ (proj2 G).1, fun a =>
      ap (proj2 F).1 _ _ ((proj2 G).2 (f a)) • (proj2 F).2 a⟩

def equiv_comp {A B C : Type} (e : equiv A B) (d : equiv B C) : equiv A C :=
  ⟨d.1 ∘ e.1, is_equiv_comp e.2 d.2⟩

def is_equiv_triangle_top {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (F : is_equiv f) (G : is_equiv g) : is_equiv h :=
  let I := has_inverse_of_is_equiv G
  is_equiv_of_htpy (inv_htpy (triangle_retr H ⟨I.1, proj2 I.2⟩))
    (is_equiv_comp F (is_equiv_inv ⟨g, G⟩))

def is_equiv_triangle_right {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (F : is_equiv f) (E : is_equiv h) : is_equiv g :=
  is_equiv_of_htpy (inv_htpy (triangle_sec H (proj1 E)))
    (is_equiv_comp (is_equiv_inv ⟨h, E⟩) F)

def is_equiv_triangle_left {A B X : Type} {f : A → X} {g : B → X} {h : A → B}
    (H : htpy f (g ∘ h)) (G : is_equiv g) (E : is_equiv h) : is_equiv f :=
  is_equiv_of_htpy (inv_htpy H) (is_equiv_comp E G)

def is_equiv_section {A B : Type} {f : A → B} (E : is_equiv f) (s : sec f) :
    is_equiv s.1 :=
  is_equiv_triangle_top (inv_htpy s.2) (equiv_id B).2 E

def is_equiv_retraction {A B : Type} {f : A → B} (E : is_equiv f) (r : retr f) :
    is_equiv r.1 :=
  is_equiv_triangle_right (inv_htpy r.2) (equiv_id A).2 E

/- Exercise 9.5: interchange of dependent sums. -/
def equiv_sigma_swap {A B : Type} (C : A → B → Type) :
    equiv (Σ x, Σ y, C x y) (Σ y, Σ x, C x y) :=
  equiv_of_inverse (fun s => ⟨s.2.1, s.1, s.2.2⟩) (fun s => ⟨s.2.1, s.1, s.2.2⟩)
    (fun _ => MyEq.refl _) (fun _ => MyEq.refl _)

def equiv_sigma_fiber_swap {A : Type} (B C : A → Type) :
    equiv (Σ u : (Σ x, B x), C u.1) (Σ v : (Σ x, C x), B v.1) :=
  equiv_of_inverse (fun s => ⟨⟨s.1.1, s.2⟩, s.1.2⟩) (fun s => ⟨⟨s.1.1, s.2⟩, s.1.2⟩)
    (fun _ => MyEq.refl _) (fun _ => MyEq.refl _)

/- Exercise 9.6: the functorial action on coproducts (Lean's existing Sum.map). -/
def map_sum_id (A B : Type) : htpy (Sum.map (@id A) (@id B)) id
  | Sum.inl _ => MyEq.refl _
  | Sum.inr _ => MyEq.refl _

def map_sum_comp {A A' A'' B B' B'' : Type}
    (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') :
    htpy (Sum.map (f' ∘ f) (g' ∘ g)) (Sum.map f' g' ∘ Sum.map f g)
  | Sum.inl _ => MyEq.refl _
  | Sum.inr _ => MyEq.refl _

def map_sum_htpy {A A' B B' : Type} {f f' : A → A'} {g g' : B → B'}
    (H : htpy f f') (K : htpy g g') : htpy (Sum.map f g) (Sum.map f' g')
  | Sum.inl a => ap Sum.inl _ _ (H a)
  | Sum.inr b => ap Sum.inr _ _ (K b)

def is_equiv_map_sum {A A' B B' : Type} {f : A → A'} {g : B → B'}
    (F : is_equiv f) (G : is_equiv g) : is_equiv (Sum.map f g) :=
  let I := has_inverse_of_is_equiv F
  let J := has_inverse_of_is_equiv G
  is_equiv_of_has_inverse ⟨Sum.map I.1 J.1, myProd.mk
    (fun s => match s with
      | Sum.inl a => ap Sum.inl _ _ (proj1 I.2 a)
      | Sum.inr b => ap Sum.inr _ _ (proj1 J.2 b))
    (fun s => match s with
      | Sum.inl a => ap Sum.inl _ _ (proj2 I.2 a)
      | Sum.inr b => ap Sum.inr _ _ (proj2 J.2 b))⟩

def equiv_sum_map {A A' B B' : Type} (e : equiv A A') (d : equiv B B') :
    equiv (A ⊕ B) (A' ⊕ B') := ⟨Sum.map e.1 d.1, is_equiv_map_sum e.2 d.2⟩

/- Exercise 9.7: the functorial action on the project's myProd. -/
def map_prod {A A' B B' : Type} (f : A → A') (g : B → B') : myProd A B → myProd A' B'
  | myProd.mk a b => myProd.mk (f a) (g b)

def map_prod_id (A B : Type) : htpy (map_prod (@id A) (@id B)) id
  | myProd.mk _ _ => MyEq.refl _

def map_prod_comp {A A' A'' B B' B'' : Type}
    (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') :
    htpy (map_prod (f' ∘ f) (g' ∘ g)) (map_prod f' g' ∘ map_prod f g)
  | myProd.mk _ _ => MyEq.refl _

def map_prod_htpy {A A' B B' : Type} {f f' : A → A'} {g g' : B → B'}
    (H : htpy f f') (K : htpy g g') : htpy (map_prod f g) (map_prod f' g')
  | myProd.mk a b =>
      ap (fun x => myProd.mk x (g b)) _ _ (H a) • ap (myProd.mk (f' a)) _ _ (K b)

def is_equiv_map_prod {A A' B B' : Type} {f : A → A'} {g : B → B'}
    (F : is_equiv f) (G : is_equiv g) : is_equiv (map_prod f g) :=
  let I := has_inverse_of_is_equiv F
  let J := has_inverse_of_is_equiv G
  is_equiv_of_has_inverse ⟨map_prod I.1 J.1, myProd.mk
    (concat_htpy (inv_htpy (map_prod_comp I.1 f J.1 g))
      (concat_htpy (map_prod_htpy (proj1 I.2) (proj1 J.2)) (map_prod_id _ _)))
    (concat_htpy (inv_htpy (map_prod_comp f I.1 g J.1))
      (concat_htpy (map_prod_htpy (proj2 I.2) (proj2 J.2)) (map_prod_id _ _)))⟩

def equiv_prod_map {A A' B B' : Type} (e : equiv A A') (d : equiv B B') :
    equiv (myProd A B) (myProd A' B') := ⟨map_prod e.1 d.1, is_equiv_map_prod e.2 d.2⟩

-- 9.7(e), valid forward implication, with exactly the printed domains A and B.
def factors_of_is_equiv_map_prod {A A' B B' : Type} {f : A → A'} {g : B → B'}
    (E : is_equiv (map_prod f g)) : myProd (B → is_equiv f) (A → is_equiv g) :=
  let I := has_inverse_of_is_equiv E
  myProd.mk
    (fun b => is_equiv_of_has_inverse ⟨fun a' => proj1 (I.1 (myProd.mk a' (g b))), myProd.mk
      (fun a' => ap proj1 _ _ (proj1 I.2 (myProd.mk a' (g b))))
      (fun a => ap proj1 _ _ (proj2 I.2 (myProd.mk a b)))⟩)
    (fun a => is_equiv_of_has_inverse ⟨fun b' => proj2 (I.1 (myProd.mk (f a) b')), myProd.mk
      (fun b' => ap proj2 _ _ (proj1 I.2 (myProd.mk (f a) b')))
      (fun b => ap proj2 _ _ (proj2 I.2 (myProd.mk a b)))⟩)

/- The converse of 9.7(e) on p. 114 of the supplied 2022 edition is false.
   For A = B = Empty and A' = B' = Unit, condition (ii) holds vacuously,
   whereas the map of products has no section. These are explicit witnesses,
   rather than an additional assumption or a silently changed statement. -/
def exercise_9_7e_condition_ii :
    myProd (Empty → is_equiv (fun _ : Empty => ()))
      (Empty → is_equiv (fun _ : Empty => ())) :=
  myProd.mk Empty.elim Empty.elim

def exercise_9_7e_not_condition_i :
    myNegType (is_equiv (map_prod (fun _ : Empty => ()) (fun _ : Empty => ()))) :=
  fun E => proj1 ((proj1 E).1 (myProd.mk () ()))

/- Exercise 9.8: addition and multiplication of finite types. -/
def equiv_fin_add (k : myN) : (l : myN) → equiv (myFin (myAdd k l)) (myFin k ⊕ myFin l)
  | myN.zero => equiv_inv (equiv_sum_empty (myFin k))
  | myN.succ l => equiv_comp
      (equiv_sum_map (equiv_fin_add k l) (equiv_id Unit))
      (equiv_sum_assoc (myFin k) (myFin l) Unit)

def equiv_fin_mult (k : myN) : (l : myN) →
    equiv (myFin (myMult k l)) (myProd (myFin k) (myFin l))
  | myN.zero => equiv_inv (equiv_prod_empty (myFin k))
  | myN.succ l =>
      equiv_comp (equiv_fin_add k (myMult k l))
        (equiv_comp (equiv_sum_map (equiv_id (myFin k)) (equiv_fin_mult k l))
          (equiv_comp (equiv_sum_comm (myFin k) (myProd (myFin k) (myFin l)))
            (equiv_comp (equiv_sum_map (equiv_id (myProd (myFin k) (myFin l)))
                (equiv_inv (equiv_prod_unit (myFin k))))
              (equiv_inv (equiv_prod_sum (myFin k) (myFin l) Unit)))))

/- Exercise 9.9: finitely cyclic maps. Reuse iteration from Exercise 8.1. -/
open chapter8 (iterate)

def is_finitely_cyclic {X : Type} (f : X → X) : Type :=
  (x y : X) → Σ k : myN, iterate f k x ≡ y

def iterate_succ_input {X : Type} (f : X → X) : (n : myN) → (x : X) →
    iterate f n (f x) ≡ f (iterate f n x)
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x => ap f _ _ (iterate_succ_input f n x)

def iterate_comm {X : Type} (f : X → X) : (n m : myN) → (x : X) →
    iterate f n (iterate f m x) ≡ iterate f m (iterate f n x)
  | myN.zero, _, _ => MyEq.refl _
  | myN.succ n, m, x => ap f _ _ (iterate_comm f n m x) •
      myEq_symm (iterate_succ_input f m (iterate f n x))

-- A positive period at x transports to every point in the orbit of x.
def injective_of_finitely_cyclic {X : Type} {f : X → X} (C : is_finitely_cyclic f)
    (x y : X) (p : f x ≡ f y) : x ≡ y :=
  let r := C (f x) x
  let s := C x y
  let hx : iterate f r.1.succ x ≡ x := myEq_symm (iterate_succ_input f r.1 x) • r.2
  let hy : iterate f r.1.succ y ≡ y :=
    ap (iterate f r.1.succ) _ _ (myEq_symm s.2) •
    iterate_comm f r.1.succ s.1 x • ap (iterate f s.1) _ _ hx • s.2
  myEq_symm r.2 • ap (iterate f r.1) _ _ p • iterate_succ_input f r.1 y • hy

def sec_of_finitely_cyclic {X : Type} {f : X → X} (C : is_finitely_cyclic f) : sec f :=
  ⟨fun y => iterate f (C (f y) y).1 y,
    fun y => myEq_symm (iterate_succ_input f (C (f y) y).1 y) • (C (f y) y).2⟩

def is_equiv_of_finitely_cyclic {X : Type} {f : X → X}
    (C : is_finitely_cyclic f) : is_equiv f :=
  let s := sec_of_finitely_cyclic C
  is_equiv_of_has_inverse ⟨s.1, myProd.mk s.2
    (fun x => injective_of_finitely_cyclic C (s.1 (f x)) x (s.2 (f x)))⟩

-- add_nat_fin and iterate compute by the same recursion; this relates the
-- existing finite translation operation to the generic notion of cyclicity.
def iterate_succ_fin (k : myN) : (n : myN) → (x : myFin k) →
    iterate (succ_fin k) n x ≡ add_nat_fin k n x
  | myN.zero, _ => MyEq.refl _
  | myN.succ n, x => ap (succ_fin k) _ _ (iterate_succ_fin k n x)

def is_finitely_cyclic_succ_fin : (k : myN) → is_finitely_cyclic (succ_fin k)
  | myN.zero, e, _ => nomatch e
  | myN.succ k, x, y =>
      let a := add_fin k.succ (neg_fin k.succ x) y
      ⟨inclusion k.succ a,
        iterate_succ_fin k.succ (inclusion k.succ a) x •
        myEq_symm (add_fin_assoc k.succ x (neg_fin k.succ x) y) •
        ap (fun t => add_fin k.succ t y) _ _ (add_fin_right_inverse k x) •
        add_nat_fin_zero_inclusion k y⟩

end chapter9
