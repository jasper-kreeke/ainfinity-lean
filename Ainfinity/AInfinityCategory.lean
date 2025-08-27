import Mathlib

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject


namespace AInfinityCategoryTheory

/- Blueprint:

-- Quiver struct
-- graded chain of morphisms
-- chain of morphisms (optional)

-- total degree
-- sign
-- ∀ graded chains of morphisms: correct degree
-- ∀ graded chains of morphisms: A∞-rels with signs

-/

universe a
variable (C : Type a) [Category C]



/- Examples:
-- Cpow i is meant to denote the vector space ℂ^i.
def Cpow (i : ℕ) := Fin i → ℂ
#check Cpow 6

-- sample quiver: obj = Fin 1; β = ℤ; data(0, 0) = i ↦ ℂ^i
def sample_quiver : GQuiver ℤ (Fin 1) :=
  {data := fun X Y ↦ (fun i ↦ if i ≥ 0 then Cpow i.toNat else Cpow 0: (GradedObject ℤ Type))}

-- test extracting Hom^3 type.
def three_dimensional_space := (sample_quiver.data 0 0) 3
def five_five_five_vector : three_dimensional_space := fun j ↦ (5 : ℂ)
-/


/-
Design question: Should we implement Hom(X, Y) = ⊕ Hom^i (X, Y) or keep all Hom's graded?

In the below implementation, Hom is a Pi type which is not what the A∞ homs are.
Rather we need a direct sum type (not to be confused with Sigma type),
i.e. a function which takes inputs (b : β) and outputs elements of type (self.data […])
but only has nonzero values on finitely many b's. How to do it efficiently?

def GQuiver.Hom {β : Type} {V : Type} [self : GQuiver β V] (X Y : V) : Type :=
  Π b, self.data (β:=β) X Y b
open GQuiver

inductive GChain {β : Type} {obj : Type} [self : GQuiver β obj] : obj → obj → Type where
  | nil : {X Y : obj} → (self.Hom β X Y) → GChain (β:=β) X Y
  | cons : {X Y Z : obj} → GChain (β:=β) X Y → (self.Hom β Y Z) → GChain (β:=β) X Z
-/

/-
  A non-unital $$A_∞$$ category is the data of all $$μ^d$$ compositions of $d$ morphisms
  for all $$d ∈ ℕ, d ≥ 1$$, subject to the conditions written in the AInfinityCategory class.

  $$μ^1$$ is called the "differential."
  $$μ^2$$ will be the usual composition.

Implementation philosophy:

1) There are various more or less correct ways to implement the datum of A∞-products:
a) for all non-homogeneous chains simultaneously.
b) for homogeneous chains only, and the datum includes proof that the output has the correct degree.
c) for homogeneous chains only, and not requiring that the output has a correct degree.
We decided to stick with option c). In particular this means that μ takes an additional parameter
output_deg.

2) The μ = mu method.

inputs:
X Y : two objects
chain : a HomogeneousChain a_1, …, a_k from X to Y
output_deg : an element of type β

outputs:
the part of μ^k (a_k, …, a_1) lying in degree output_deg.
It is of type ((self.data X Y) output_deg).

-/

-- Its type is Type (max u v (w+1))
class AInfinityCategoryStruct.{u, v, w} (β : Type u) [GradingCore β] (obj : Type v) extends GQuiver.{u, v, w} β obj where
  /-- All possible compositions of chains of morphisms. -/
  mu {X Y : obj} (chain : HomogeneousChain toGQuiver X Y) (output_deg : β) :
    let correct_degree := HomogeneousChain.correct_output_degree chain
    (toGQuiver.data X Y) correct_degree

scoped infixr:80 " μ " => AInfinityCategoryStruct.mu -- type as \mu

-- TODO: lift this from the usual Quiver to the GQuiver
-- initialize_simps_projections AInfinityCategoryStruct (-toQuiver_Hom)

-- set_option diagnostics true


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
