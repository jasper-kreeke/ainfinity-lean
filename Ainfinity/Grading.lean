import Mathlib

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject


namespace AInfinityCategoryTheory


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



class GQuiver.{u, v, w} (β : Type u) (obj : Type v) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  data : obj → obj → GradedObject β (Type w)


end AInfinityCategoryTheory
