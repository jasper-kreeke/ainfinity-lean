import Mathlib

import Ainfinity.Grading
import Ainfinity.HomogeneousChain

/- open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject -/

-- This one necessary (in current implementation) for the expand
attribute [local instance] Classical.decEq
noncomputable section

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
  mu {X Y : obj} (chain : HomogeneousChain X Y): (toGQuiver.data X Y) (correct_output_deg chain)

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

-- Convenience: the inhomogeneous Hom type at (X,Y)
abbrev InHom {β : Type u} [GradingCore β] {obj : Type v}
  (C : AInfinityPreadditive.{u,v,w} β obj) (X Y : obj) : Type _ :=
  (toInhomQuiver C).Hom X Y

/-
**expand**
helper function to perform multilinear expansion of μ.

input:
  `acc`  = (vₖ, …, v_{ℓ+1}), a homogeneous chain Y ⟶ Z
  `rest` = (v_ℓ, …, v₁), an inhomogeneous chain X ⟶ Y

output:
  μ(vₖ, …, v₁), as an inhomogeneous morphism X ⟶ Z

procedure:
  * if ℓ = 0:
      evaluate μ on the homogeneous chain `acc`,
      place the result in the DFinsupp fiber indexed by its output degree.
  * if ℓ > 0:
      - split `v_ℓ` into graded components `(d,m)`,
      - call `expand` on (vₖ, …, v_{ℓ+1}, m) and (v_{ℓ-1}, …, v₁),
      - finally sum over all choices for `d` using `DFinsupp.sum`.

  * the `sorry`s currently stand in for decidability and AddCommMonoid
    obligations needed to run `DFinsupp.sum`.
  * once those are filled, the “aux2/aux3/refine” scaffolding can
    likely be inlined into a single `exact e.sum (γ := …) …`.
-/
def expand {β : Type u} [GradingCore β]
  {obj : Type v} (C : AInfinityPreadditive.{u,v,w} β obj)
  {X Y Z: obj}
  (acc : HomogeneousChain (gquiver := C.toGQuiver) Y Z)
  (rest : InhomogeneousChain (C := C) X Y) :
  InHom (C) X Z := by

  cases rest with

  -- case nil
  | nil =>
  let b := correct_output_deg (gquiver := C.toGQuiver) acc
  let _ : AddCommMonoid ((C.data X Z) b) := C.hom_is_monoid X Z b
  let _ : ∀ i, Zero ((C.data X Z) i) := fun i =>
    addcommmonoid_to_zero (C.hom_is_monoid X Z i)
  exact DFinsupp.single b (C.toAInfinityCategoryStruct.mu (β := β) (obj := obj) acc)

  -- case cons
  | @cons Y' _ most e =>
  let summing_func := fun d (m : (C.data Y' Y) d) =>
    let m_as_path : @Quiver.Path obj (toQuiver C.toGQuiver) Y' Y :=
      @Quiver.Hom.toPath obj (toQuiver C.toGQuiver) Y' Y ⟨d, m⟩
    let new_acc : HomogeneousChain (gquiver := C.toGQuiver) Y' Z := @Quiver.Path.comp obj (toQuiver C.toGQuiver) Y' Y Z m_as_path acc
    expand C new_acc most

  /- Complete and inline this later on. -/
  have aux2 := @e.sum (γ := (InHom C X Z))
  have dec : DecidableEq β := by sorry
  have aux3 := aux2 dec
  refine aux3 ?dec2 ?add summing_func
  -- prove dec2
  · sorry
  -- prove add
  · sorry

/-
**mu_on_inhomogeneous_chain**
multilinear expansion of μ on inhomogeneous chains.

input: (v_k, …, v_1).
output: μ(v_k, …, v_1).
-/
def mu_on_inhomogeneous_chain
  {β : Type u} [GradingCore β]
  {obj : Type v} (C : AInfinityPreadditive.{u,v,w} β obj)
  {X Y : obj}
  (chain : InhomogeneousChain (C := C) X Y) :
  InHom C X Y :=
  -- start with empty homogeneous accumulator (X = Z)
  expand C (@Quiver.Path.nil obj (toQuiver C.toGQuiver) Y) chain




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
