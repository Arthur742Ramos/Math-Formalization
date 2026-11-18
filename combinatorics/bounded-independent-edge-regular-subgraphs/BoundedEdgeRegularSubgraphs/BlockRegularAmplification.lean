module

public import BoundedEdgeRegularSubgraphs.IndependentEdgeFamilies
public import BoundedEdgeRegularSubgraphs.OrderUpper
import Mathlib.Tactic

/-!
# Amplifying exact-order regularity across independent blocks
-/

public section

open Function MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem measurableSet_exactOrderEvent (k : ℕ) :
    MeasurableSet (exactOrderEvent (α := α) k) := by
  classical
  unfold exactOrderEvent
  apply MeasurableSet.iUnion
  intro S
  exact measurableSet_regularEvent.preimage
    (measurable_pi_iff.mpr (fun e ↦ measurable_pi_apply (inducedEdge S.val e)))

private noncomputable def setMapOrderIso (S : Finset α) (T : Finset ↥S) :
    ↥T ≃o ↥(T.map ⟨Subtype.val, Subtype.val_injective⟩) where
  toFun i := ⟨i.val.val, Finset.mem_map.mpr ⟨i.val, i.property, rfl⟩⟩
  invFun i := by
    let h := Finset.mem_map.mp i.property
    exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    let h : i.val.val ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩ :=
      Finset.mem_map.mpr ⟨i.val, i.property, rfl⟩
    let H := Finset.mem_map.mp h
    change (Classical.choose H).val = i.val.val
    exact (Classical.choose_spec H).2
  right_inv i := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_map.mp i.property)).2
  map_rel_iff' := Iff.rfl

/-- An exact-order regular induced graph inside a block is also an
exact-order regular induced graph of the original array. -/
theorem induce_preimage_exactOrder_subset (S : Finset α) (k : ℕ) :
    induce S ⁻¹' (exactOrderEvent (α := ↥S) k) ⊆ exactOrderEvent (α := α) k := by
  classical
  intro w hw
  obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hw
  let U := T.val.map ⟨Subtype.val, Subtype.val_injective⟩
  let f : ↥T.val ≃o ↥U := setMapOrderIso S T.val
  have hU : U.card = k := by rw [show U = T.val.map _ by rfl, Finset.card_map, T.property]
  apply Set.mem_iUnion.mpr
  refine ⟨⟨U, hU⟩, ?_⟩
  change ∀ i j : U, degreeSum (induce U w) i = degreeSum (induce U w) j
  change ∀ i j : T.val, degreeSum (induce T.val (induce S w)) i =
    degreeSum (induce T.val (induce S w)) j at hT
  have he : induce T.val (induce S w) = induce U w ∘ edgeEquiv f := by
    funext e
    rfl
  rw [he] at hT
  simp_rw [degreeSum_reindex f] at hT
  intro i j
  simpa only [f.apply_symm_apply] using hT (f.symm i) (f.symm j)

/-- A uniform positive success probability in each deterministic
disjoint block gives an exponential upper bound on global failure. -/
theorem probability_exactOrder_failure_le_of_disjoint_blocks {ι : Type*} [Fintype ι]
    (p : Edge α → Icc (0 : ℝ) 1) (S : ι → Finset α) (hS : Pairwise (Disjoint on S))
    (k : ℕ) {p₀ : ℝ} (h₀ : 0 ≤ p₀) (h₁ : p₀ ≤ 1)
    (hSucc : ∀ i, p₀ ≤ (graphLaw (induce (S i) p)).real (exactOrderEvent k)) :
    (graphLaw p).real (exactOrderEvent (α := α) k)ᶜ ≤
      Real.exp (-p₀ * (Fintype.card ι : ℝ)) := by
  classical
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  let E (i : ι) := (exactOrderEvent (α := ↥(S i)) k)ᶜ
  have hE (i : ι) : MeasurableSet (E i) := (measurableSet_exactOrderEvent k).compl
  have hi (i : ι) : (graphLaw (induce (S i) p)).real (E i) ≤ 1 - p₀ := by
    have : IsProbabilityMeasure (graphLaw (induce (S i) p)) := by unfold graphLaw; infer_instance
    unfold E
    rw [probReal_compl_eq_one_sub (measurableSet_exactOrderEvent k)]
    linarith only [hSucc i]
  have hsub : (exactOrderEvent (α := α) k)ᶜ ⊆ {w | ∀ i, induce (S i) w ∈ E i} := by
    intro w hw i hi
    exact hw (induce_preimage_exactOrder_subset (S i) k hi)
  calc
    _ ≤ (graphLaw p).real {w | ∀ i, induce (S i) w ∈ E i} := measureReal_mono hsub
    _ = ∏ i, (graphLaw (induce (S i) p)).real (E i) :=
      probability_induced_disjoint_family p S hS E hE
    _ ≤ ∏ _i : ι, (1 - p₀) := Finset.prod_le_prod₀
      (fun _ _ ↦ measureReal_nonneg) (fun i _ ↦ hi i)
    _ ≤ ∏ _i : ι, Real.exp (-p₀) := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ sub_nonneg.mpr h₁)
      intro i _
      have h := Real.add_one_le_exp (-p₀)
      linarith only [h]
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, mul_comm]

end BoundedEdgeRegularSubgraphs
