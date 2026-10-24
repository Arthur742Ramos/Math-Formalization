module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Tactic

@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology
namespace EZero

/-- The actual binary product, with its inferred product topology. -/
abbrev CantorSpace := ℕ → Bool
/-- Eventual equality of values, not a permutation of coordinates. -/
abbrev E0 (x y : CantorSpace) : Prop := ∃ N : ℕ, ∀ n, N ≤ n → x n = y n
/-- Every open inverse image has the property of Baire. -/
abbrev BPPreimages {Y : Type*} [TopologicalSpace Y] (f : CantorSpace → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- Coordinatewise xor by a fixed binary mask is an involutive homeomorphism. -/
def maskHomeomorph (m : ℕ → Bool) : CantorSpace ≃ₜ CantorSpace where
  toFun x n := Bool.xor (m n) (x n)
  invFun x n := Bool.xor (m n) (x n)
  left_inv x := by
    funext n
    change Bool.xor (m n) (Bool.xor (m n) (x n)) = x n
    cases m n <;> cases x n <;> rfl
  right_inv x := by
    funext n
    change Bool.xor (m n) (Bool.xor (m n) (x n)) = x n
    cases m n <;> cases x n <;> rfl
  continuous_toFun := continuous_pi fun n =>
    (continuous_of_discreteTopology : Continuous (Bool.xor (m n))).comp (continuous_apply n)
  continuous_invFun := continuous_pi fun n =>
    (continuous_of_discreteTopology : Continuous (Bool.xor (m n))).comp (continuous_apply n)

@[simp] theorem maskHomeomorph_apply (m : ℕ → Bool) (x : CantorSpace) (n : ℕ) :
    maskHomeomorph m x n = Bool.xor (m n) (x n) := rfl

/-- Flip exactly the finite set of indicated coordinates. -/
def flip (s : Finset ℕ) : CantorSpace ≃ₜ CantorSpace :=
  maskHomeomorph (fun n => decide (n ∈ s))

theorem e0_flip (s : Finset ℕ) (x : CantorSpace) : E0 x (flip s x) := by
  refine ⟨s.sup id + 1, ?_⟩
  intro n hn
  have hs : n ∉ s := by
    intro h
    have hm := Finset.le_sup (f := id) h
    simp only [id_eq] at hm
    omega
  simp [flip, hs]

end EZero
