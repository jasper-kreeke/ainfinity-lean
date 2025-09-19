import Mathlib

import Ainfinity.Grading
import Ainfinity.HomogeneousChain

/- open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject -/


namespace AInfinityCategoryTheory

/- Blueprint:

-- total degree
-- sign
-- ∀ graded chains of morphisms: correct degree
-- ∀ graded chains of morphisms: A∞-rels with signs

Tasks:
1) Define μ: Chain → Hom
2) tilde{μ}: Inhomogeneous chains → Hom
3) [obsolete by Kim Morrison's advice]
4) implement A∞ relations for μ
5) if μ satisfies A∞-relations, then also tilde{μ}.

Jasper: 1+2
Marco: 3+4
-/


-- Its type is Type (max u v (w+1))
class AInfinityCategoryStruct.{u, v, w} (β : Type u) [GradingCore β] (obj : Type v) extends GQuiver.{u, v, w} β obj where
  /-- All possible compositions of chains of morphisms. -/
  μ {X Y : obj} (chain : HomogeneousChain X Y): (toGQuiver.data X Y) (correct_output_deg chain)

scoped infixr:80 " μ " => AInfinityCategoryStruct.mu -- type as \mu

/-
-- Design philosophy: Layer A∞-structure by algebraic strength.
-- Start minimal (just graded sets), add structure only when needed.

| Level | Extra structure on `Hom β X Y`            | Purpose                                | Encoded in                |
|-------|-------------------------------------------|----------------------------------------|---------------------------|
| 0     | none                                      | raw graded morphisms                   | `GQuiver`                 |
| 1     | `AddCommMonoid` (or `AddCommGroup`)       | signs, sums, linear μₙ                 | `AInfinityPreadditive`    |
| 2     | `Module R` over a `Semiring R`            | scalar multiplication, linearity       | `AInfinityLinear R`       |
| 3     | `Module R` over a `Semiring R`            | A∞-relations hold over R               | `AInfinityCategory R`     |

Unitality comes after this!

Use only as much structure as your use case requires.
-/

@[pp_with_univ, stacks 0014]
class AInfinityPreadditive.{u,v,w} (β : Type u) [GradingCore β] (obj : Type v) extends AInfinityCategoryStruct.{u,v,w} β obj where
  hom_is_monoid: ∀ (X Y : obj) (b : β), AddCommMonoid ((toGQuiver.data X Y) b)

def addcommmonoid_to_zero {G : Type u} (s : AddCommMonoid G) : Zero.{u} G where
  zero := (0 : G)

@[simp]
def toInhomQuiver {β : Type u} [GradingCore β] {obj : Type v} (C : AInfinityPreadditive.{u, v, w} β obj) : Quiver obj where
  Hom X Y := @DFinsupp β (C.data X Y) (fun i ↦ addcommmonoid_to_zero (C.hom_is_monoid X Y i))

abbrev InhomogeneousChain.{u, v, w} {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} (X : obj) (Y : obj) :=
  @Quiver.Path obj (toInhomQuiver C) X Y

/-
Plan:
β, length ↦ β^length
inhom_path ↦ (function β^length → homog_path)
inhom_path ↦ (β^length → homog_path →(μ) final chains)
inhom_path ↦ Sum (final chains)
-/

/-
Alternative plan:
inhom path of length 1 ↦ (function β → homogeneous_chain)
inhom path of length 2 ↦ (function β → (function β → homogeneous_chain))
inhom path of length 3 ↦ (function β → (function β → (function β → homogeneous_chain)))

Now sum:
for an inhom path of length 1 is simply dfinsupp.sum of that function
for an inhom path of length 2 is summing up and for each i : β it should add the
  β → homogeneous chain  item, but not as a function but if you add them up you should
  instead do a different addition namely μ(v_1, -, …)
  i.e. g should turn a function β → homogeneous chain into inhomogeneous_chain.
  In other words g is the same function with one less recursion depth.
-/

def el : DFinsupp (fun n : ℕ ↦ ℤ) := by
  have aux : ℕ → ℤ := by
    intro n
    match n with
    | 0 => exact 5
    | i+1 => exact 0
  use aux
  -- use Trunc.mk { s // ∀ (i : ℕ), i ∈ s ∨ aux i = 0 }

/-
structure TEST where
  A : ℕ
  B : ℤ

def test : TEST := by
  refine ⟨?S, ?T⟩
-/

/-
def get_huge_type {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) (offset : ℕ) : Type _ :=
  match offset with
  | k ≤ chain.length => @DFinsupp β get_huge_type chain (offset + 1))
  | chain.length =>
-/

-- for length = 1
def add_up_1 chain : Hom :=
  coercer = el ↦ μ(el)
  first = chain.first
  first.sum coercer

def add_up_2 chain : Hom :=
  coercer = el1 ↦ add_up [μ(el1, ); chain]
  first = chain.first
  first.sum coercer

-- for length = 1
def add_up_1 {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) {h : @Quiver.Path.length obj (toInhomQuiver C) X Y chain = 1} : (toInhomQuiver C).Hom X Y :=
  match chain with
  | @Quiver.Path.nil obj (toInhomQuiver C) _ => sorry
  | @Quiver.Path.cons obj (toInhomQuiver C) _ _ _ most last => by
    dsimp at last
    have components : b : β ↦ last b : (toInhomQuiver C).Hom X Y b)
    have dfinsupp := @DFinsupp β

def create_large_evaluation {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) : (toInhomQuiver C).Hom X Y :=



def add_up {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) : (toInhomQuiver C).Hom X Y :=
  match chain with
  | @Quiver.Path.nil obj (toInhomQuiver C) _ => by dsimp; exact 0
  | @Quiver.Path.cons obj (toInhomQuiver C) _ _ _ most last => by
    dsimp
    -- have h : (i : β) → Zero (C.data X Y i) := sorry
    -- refine ⟨?func, ?supp_hyp⟩
    have aux := fun b : β ↦ add_up most

def get_grading_combo_type {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) : Type u :=
  Fin (@Quiver.Path.length obj (toInhomQuiver C) X Y chain) → β

/-
def inhomog_path_into_components {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) : ℕ :=
  let combo_type := get_grading_combo_type chain
  let combo_map := fun combo : combo_type ↦ chain
  -- (combo : combo_type) →
  5
-/

def μ_on_inhomogeneous {β : Type u} [GradingCore β] {obj : Type v} {C : AInfinityPreadditive.{u, v, w} β obj} {X : obj} {Y : obj} (chain : InhomogeneousChain.{u, v, w} (C := C) X Y) : (toInhomQuiver C).Hom X Y :=
  sorry




@[pp_with_univ, stacks 0014]
class AInfinityLinear.{u,v,w,x} (β : Type u) [GradingCore β] (obj : Type v) (R : Type x) [Semiring R] extends AInfinityPreadditive.{u,v,w} β obj where
  hom_is_module : ∀ (X Y : obj) (b : β), Module R ((toGQuiver.data X Y) b)
  hom_is_monoid := by
      intro X Y b
      -- `Module R _` → `AddCommMonoid _` is an instance in mathlib
      infer_instance
  mu_is_multilinear :
    {X Y : obj} →
    (chain : HomogeneousChain toGQuiver X Y) →
    (index : ℕ) →
    let X_i :=
    let Y_i :=
    (alternative : toGQuiver )

/- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
/-
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    aesop_cat
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    aesop_cat
-/

/-
/- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    aesop_cat
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
    aesop_cat
-/

/-
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat

class AInfinityLinear (K : Type u) [Field K]
  (A : Type u) [AInfinityCategory.{max (max u v)} A] [Preadditive A]  where
  homModule : ∀ X Y : A, Gmodule K (X ⟶ Y) := by infer_instance
  add_comp : ∀ (P Q R : A) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    aesop_cat
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
    aesop_cat
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : A) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    aesop_cat
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : A) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    aesop_cat

-/
