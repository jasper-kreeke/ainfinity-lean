import Mathlib

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject


namespace AInfinityCategoryTheory


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

def sub_in_bounds {a b c : PNat} (h : a ≤ b) (h' : b ≤ c): a ≤ c := by
  calc
    a ≤ b := by exact h
    _ ≤ c := by exact h'

def HomogeneousChain.subchain {β : Type u} [inst: GradingCore β] {obj : Type v} {quiver : GQuiver.{u, v, w} β obj} {X Y : obj} (chain : HomogeneousChain.{u,v,w} quiver X Y) (first : PNat) (last : PNat) {in_order: first ≤ last} {in_bounds : last ≤ HomogeneousChain.length chain}: HomogeneousChain quiver
  (@HomogeneousChain.index_object β inst obj quiver X Y chain first (le_trans in_order in_bounds))
  (@HomogeneousChain.index_object β inst obj quiver X Y chain last in_bounds) := by
  have difference : Nat := last - first
  cases hdiff : difference
  have that_object := @HomogeneousChain.index_object β inst obj quiver X Y chain first (le_trans in_order in_bounds)
  exact HomogeneousChain.longer
    that_object
    HomogeneousChain.empty
  --| k+1 => HomogeneousChain.longer


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

end AInfinityCategoryTheory
