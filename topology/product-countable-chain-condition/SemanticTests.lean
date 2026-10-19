module
public import ProductCCCSolution
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order
public import Mathlib.Analysis.Real.Cardinality
open ProductCCC Set TopologicalSpace Function

-- Empty index, empty factors and a genuinely larger index universe.
example : HasCCC (Empty → Bool) := hasCCC_pi_of_separable
example : HasCCC (ℝ → Empty) := hasCCC_pi_of_separable
example : HasCCC (ULift.{2} ℝ → Bool) := hasCCC_pi_of_separable
example : HasCCC (Set (ℕ → Bool) → Bool) := hasCCC_pi_of_separable
example : HasCCC (ℝ → ℝ) := hasCCC_pi_of_separable
example : HasCCC (Set ℝ → Unit) := hasCCC_pi_of_separable

-- Repeated supports are legitimate; the root may be the whole support.
example {ι : Type*} (s : Finset ι) (J : Set ℝ) :
    IsDeltaSystem (fun _ : ℝ => s) J s := by
  classical
  intro i hi j hj hij
  exact Finset.inter_self s

-- Empty-root disjoint support families.
example : IsDeltaSystem (fun i : ℝ => ({i} : Finset ℝ)) univ ∅ := by
  classical
  intro i hi j hj hij
  exact Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_singleton.mpr hij)

-- The nonempty premise in the converse is essential: the empty product-space
-- is CCC even when another (discrete uncountable) factor is not.
example : let : TopologicalSpace ℝ := ⊥
    ¬ HasCCC ℝ := by
  let : TopologicalSpace ℝ := ⊥
  have : DiscreteTopology ℝ := discreteTopology_bot ℝ
  exact fun h => (not_countable (α := ℝ)) ((hasCCC_discrete_iff ℝ).mp h)

example : let : TopologicalSpace ℝ := ⊥
    HasCCC (Empty × ℝ) := by
  let : TopologicalSpace ℝ := ⊥
  exact hasCCC_of_separable _

-- These surface contracts use actual opens, not arbitrary disjoint sets.
example {X : Type u} [TopologicalSpace X] (h : HasCCC X)
    {I : Type v} (U : I → Set X) (ho : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hd : Pairwise (Disjoint on U)) : Countable I :=
  h.countable_index U ho hne hd

-- Selected definitions have literal audited values in this independent entrypoint.
example (X : Type*) [TopologicalSpace X] : HasCCC X ↔
    ∀ A : Set (Set X), (∀ U ∈ A, IsOpen U ∧ U.Nonempty) →
      A.Pairwise Disjoint → A.Countable := Iff.rfl

example {I α : Type*} (s : I → Finset α) (J : Set I) (r : Finset α) : (by
    classical
    exact (IsDeltaSystem s J r ↔ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → s i ∩ s j = r)) := by
  classical
  exact Iff.rfl
