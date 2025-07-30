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

/- Grading policy:
In order to define A∞-relations etc., we need to assign signs to elements of the
grading type β. Policy:
• β remains arbitrary type
• Assume β has conversion to ℤ or ℤ/2ℤ
• Not assume that there is a cast ℤ → β.

In consequence,
• Sign is computed via β → (ℤ or ℤ/2ℤ) → ℤ/2ℤ
• Correct degree of μ(a_k, …, a_1) does not exist. Rather, for every output term t
  of this μ, we must have that its conversion to (ℤ or ℤ/2ℤ) given by (conv (deg t))
  satisfies (conv (deg t)) = deg a_1 + … + deg a_k + (2-k)   [inside ℤ or ℤ/2ℤ].
-/

inductive Int_or_Parity where
  | int
  | parity

/-- additive signs as ℤ/2ℤ -/
abbrev Parity := ZMod 2      -- values:  0 or 1

def correct_type (kind : Int_or_Parity) : Type 0 :=
  match kind with
  | Int_or_Parity.int => ℤ
  | Int_or_Parity.parity => Parity

class Has_Int_or_Parity.{u} (β : Type u) where
  kind : Int_or_Parity
  conv : β → (correct_type kind)

instance : Has_Int_or_Parity (ZMod 2) where
  kind := Int_or_Parity.parity
  conv := fun n ↦ n

instance : Has_Int_or_Parity ℤ where
  kind := Int_or_Parity.int
  conv := fun n ↦ n

def parityOf {β} [inst : Has_Int_or_Parity β] (d : β) : Parity := by
  cases h : inst.kind

  -- case int
  have intermediate := (inst.conv d)
  have h : correct_type (Has_Int_or_Parity.kind β) = ℤ := by
    simpa [correct_type] using congrArg correct_type h
  have result : ℤ := by
    simpa [h] using intermediate
  exact (result : Parity)

  -- case parity
  have intermediate := (inst.conv d)
  have h : correct_type (Has_Int_or_Parity.kind β) = Parity := by
    simpa [correct_type] using congrArg correct_type h
  have result : Parity := by
    simpa [h] using intermediate
  exact (result : Parity)


class GradingCore (β : Type u) extends AddCommGroup β, Has_Int_or_Parity β

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

def morphism_degree {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u,v,w} β obj} {X Y : obj} {deg : β} (morphism : (quiver.data X Y) deg) : β :=
  deg

inductive HomogeneousChain.{u, v, w} {β : Type u} [GradingCore β] {obj : Type v} (quiver : GQuiver.{u, v, w} β obj) : obj → obj → Sort _ where
  | empty {X Y : obj}  : HomogeneousChain quiver X Y
  | longer {X Y Z: obj} {deg : β} : (quiver.data X Z) deg → HomogeneousChain quiver Z Y → HomogeneousChain quiver X Y

def HomogeneousChain.total_deg {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} (chain : HomogeneousChain.{u,v,w} quiver X Y) : β :=
  match chain with
  | HomogeneousChain.empty => (0 : β)
  | HomogeneousChain.longer morphism rest => (morphism_degree morphism : β) + HomogeneousChain.total_deg rest

def HomogeneousChain.length {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} (chain : HomogeneousChain.{u,v,w} quiver X Y) : ℕ :=
  match chain with
  | HomogeneousChain.empty => (0 : ℕ)
  | HomogeneousChain.longer morphism rest => 1 + HomogeneousChain.length rest

def source {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} {b : β} (morphism : (quiver.data X Y) b) : obj :=
  X

def target {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} {b : β} (morphism : (quiver.data X Y) b) : obj :=
  Y

/-
input: chain a_1, …, a_k with a_i: X_i → X_{i+1}
input: j ∈ {1, …, k+1}
output: X_j
-/
def HomogeneousChain.index_object {β : Type u} [inst : GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} (chain : HomogeneousChain.{u,v,w} quiver X Y) (j : PNat) {in_bounds : j ≤ chain.length} : obj :=
  match chain with
  | HomogeneousChain.empty =>
    by
      have h : chain.length = 0 := by simp [length] at in_bounds
      tauto

  | HomogeneousChain.longer first rest =>
      match (j : ℕ) with
      | 0 => by
        sorry
      | 1 => source first
      | l+2 => by
        have h : 0 < l+1 := by linarith
        have l_plus_one : PNat := ⟨l+1, h⟩
        have sub_in_bounds : l_plus_one ≤ rest.length := by
          have auxiliary : (l_plus_one : ℕ) ≤ rest.length := by sorry
          tauto
        exact @HomogeneousChain.index_object β inst obj quiver (target first) Y rest l_plus_one sub_in_bounds

/-
          -- n = 1 ⇒ we're at the target of the first morphism
          by_cases h₁ : n' = 0
          · -- n = 1
            simpa [h₁] using m.trg                -- or `source m`, depending on conventions
          · -- n ≥ 2  ⇒  drop first morphism and recurse
            -- provide the new bound `n' ≤ rest.length`
            have hrest : (n' : ℕ) ≤ rest.length := by
              -- from  n' + 1 ≤ 1 + rest.length  ⇒  n' ≤ rest.length
              simpa [length, add_comm, add_left_comm] using
                (Nat.le_of_succ_le_succ (show n'.succ ≤ _ from h))
            -- build the smaller positive index `⟨n', _⟩`
            have hpos' : (0 : ℕ) < n' := by
              have : n' ≠ 0 := h₁
              exact Nat.pos_of_ne_zero this
            exact ih ⟨n', hpos'⟩ hrest
-/

/-
  | HomogeneousChain.longer first rest =>
    match j with
    | ⟨1, _⟩ => source first
    | ⟨(Nat.succ l : PNat), _⟩ => HomogeneousChain.index_object rest l
-/

#check PNat

def HomogeneousChain.subchain {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} (chain : HomogeneousChain.{u,v,w} quiver X Y) (first : PNat) (last : PNat) {in_bounds : last ≤ HomogeneousChain.length chain}: HomogeneousChain [fill this] :=
  match last with
  | first => HomogeneousChain.longer chain.first HomogeneousChain.subchain chain (first+1) last


def HomogeneousChain.correct_output_degree {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u,v,w} β obj} {X Y : obj} (chain : HomogeneousChain.{u,v,w} quiver X Y) : β :=
  (HomogeneousChain.total_deg chain) + ((2 : ℤ) - (HomogeneousChain.length chain : ℤ))

/-
input: chain a_1, …, a_k with a_i: X_i → X_{i+1}
input: j ∈ {1, …, k+1}
output: a_j
-/
def HomogeneousChain.index_morphism {β : Type u} [GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj}
  (chain : HomogeneousChain.{u,v,w} quiver X Y) (j : ℕ)
  {in_bounds : 1 ≤ j ∧ j ≤ HomogeneousChain.length chain} : (quiver.data X Y) (deg) :=

  match chain with
  | HomogeneousChain.empty => by
    simp [length] at in_bounds
    linarith
  | HomogeneousChain.longer first rest => match j with
    | 0 => first
    | k+1 => HomogeneousChain.index_morphism rest k


/-  · have empty_is_length_0 : empty.length = 0 := by sorry
    rw [empty_is_length_0] at in_bounds
    sorry

  ·
  -/
/-
  match chain with
  | HomogeneousChain.empty => -- fake! What to put here
  | HomogeneousChain.longer morphism rest => match j with
   | 0 => X -- fake
   | 1 => X
   | Nat.succ (Nat.succ k) => HomogeneousChain.index_object chain (k+1)
-/
-----------------------------


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
