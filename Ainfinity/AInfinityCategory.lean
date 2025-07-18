import Mathlib

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

noncomputable section


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

class GQuiver.{u, v, w} (β : Type u) (obj : Type v) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  data : obj → obj → GradedObject β (Type w)



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

inductive DegreeChain (β : Type) where
  | singleton : β → DegreeChain β
  | longer : β → DegreeChain β → DegreeChain β

/- Sign policy:
In order to define A∞-relations etc., we need to assign signs to elements of the
grading type β. Policy:
• β remains arbitrary type
• assume β has conversion to ±1
-/

/-- additive signs as ℤ/2ℤ -/
abbrev Sign := ZMod 2      -- values:  0 or 1
/-- A degree type that can produce a sign. -/
class HasSign (β : Type) where
  toSign : β → Sign

instance : HasSign (ZMod 2) where
  toSign n := n
instance : HasSign ℤ where
  toSign n := if Even n then 0 else 1

def signOf {β} [HasSign β] (d : β) : Sign := HasSign.toSign d

/- Chain policy:
We have the choice either to
[rigid] define chains of given length k and given sequence of objects
X_1, …, X_{k+1}, or
[loose] to define chains of arbitrary length and between arbitrary objects.

For now, we start loose for basic homological algebra and intuition.
Wrap it later in a rigid chain type when we formalize the
operations and Stasheff identities. We get ergonomic building blocks
plus a strict layer when definitional equalities really matter.
-/

def morphism_degree {β : Type} {obj : Type} {quiver : GQuiver β obj} {X Y : obj} {deg : β} (morphism : (quiver.data X Y) deg) : β :=
  deg

inductive HomogeneousChain {β : Type} {obj : Type} [HasSign β] (quiver : GQuiver β obj) : obj → obj → Type where
  | empty {X Y : obj}  : HomogeneousChain quiver X Y
  | longer {X Y Z: obj} {deg : β} : (quiver.data X Z) deg → HomogeneousChain quiver Z Y → HomogeneousChain quiver X Y

def HomogeneousChain.total_deg {β : Type} {obj : Type} [HasSign β] {quiver : GQuiver β obj} {X Y : obj} (chain : HomogeneousChain quiver X Y) : Sign :=
  match chain with
  | HomogeneousChain.empty => (0 : Sign)
  | HomogeneousChain.longer morphism rest => signOf (morphism_degree morphism) + HomogeneousChain.total_deg rest


/-
input: chain = a_1, …, a_k; j ∈ ℕ
output: ‖a_1‖ + … + ‖a_j‖
-/
def HomogeneousChain.Koszul_sign {β : Type} {obj : Type} {quiver : GQuiver β obj} {X Y : obj} [HasSign β] (chain : HomogeneousChain quiver X Y) (j : ℕ): Sign :=
  if j = 0 then
    0
  else
    match chain with
    | HomogeneousChain.empty => 0
    | HomogeneousChain.longer morphism rest => signOf (morphism_degree morphism) + HomogeneousChain.Koszul_sign rest (j - 1)


-----------------------------


def GQuiver.Hom {β : Type} {V : Type} [self : GQuiver β V] (X Y : V) : Type :=
  Π b, self.data (β:=β) X Y b

open GQuiver


inductive GChain {β : Type} {obj : Type} [self : GQuiver β obj] : obj → obj → Type where
  | nil : {X Y : obj} → (self.Hom β X Y) → GChain (β:=β) X Y
  | cons : {X Y Z : obj} → GChain (β:=β) X Y → (self.Hom β Y Z) → GChain (β:=β) X Z

/-
  A non-unital $$A_∞$$ category is the data of all $$μ^d$$ compositions of $d$ morphisms
  for all $$d ∈ ℕ, d ≥ 1$$, subject to the conditions written in the AInfinityCategory class.

  $$μ^1$$ is called the "differential."
  $$μ^2$$ will be the usual composition.
-/

class AInfinityCategoryStruct (β : Type) (obj : Type) extends GQuiver β obj : Type 2 where
  /-- All possible compositions of chains of morphisms. -/
  mu : ∀ {X Y : obj}, GChain β X Y → Hom β X Y

scoped infixr:80 " μ " => AInfinityCategoryStruct.mu -- type as \mu

-- TODO: lift this from the usual Quiver to the GQuiver
-- initialize_simps_projections AInfinityCategoryStruct (-toQuiver_Hom)

-- set_option diagnostics true

class AInfinityPreadditive [AddCommMonoid β] (obj : Type) extends AInfinityCategoryStruct β obj where
  homGroup : ∀ X Y : obj, GCommMonoid (Hom β X Y) := by infer_instance

/- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.)

@[pp_with_univ, stacks 0014]
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
-/

class AInfinityCategory (β : Type w) (obj : Type u)
  extends AInfinityCategoryStruct.{w, u, v} β obj : Type max (w+1) max u (v + 1)
  where

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

-- this fixes a general (not-yet-linear) (not-yet-small) A_∞ category
variable
-- this fixes a general type of allowed gradings of Hom-spaces (most commonly take ℤ)
variable {ι : Type v} [AddMonoid ι]

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
