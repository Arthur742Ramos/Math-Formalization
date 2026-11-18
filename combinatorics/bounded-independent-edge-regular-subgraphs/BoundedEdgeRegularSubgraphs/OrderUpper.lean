module

public import BoundedEdgeRegularSubgraphs.RegularUpper
import BoundedEdgeRegularSubgraphs.Induce
import BoundedEdgeRegularSubgraphs.UnionBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Upper bounds on the order of regular induced subgraphs
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]

omit [Fintype α] [Fintype β] in
private def edgeEquiv (f : α ≃o β) : Edge α ≃ Edge β where
  toFun e := ⟨(f e.val.1, f e.val.2), f.strictMono e.property⟩
  invFun e := ⟨(f.symm e.val.1, f.symm e.val.2), f.symm.strictMono e.property⟩
  left_inv e := Subtype.ext (Prod.ext (by simp) (by simp))
  right_inv e := Subtype.ext (Prod.ext (by simp) (by simp))

private theorem degreeSum_reindex (f : α ≃o β) (w : Edge β → ℝ) (i : α) :
    degreeSum (w ∘ edgeEquiv f) i = degreeSum w (f i) := by
  classical
  unfold degreeSum
  rw [← Equiv.sum_comp (edgeEquiv f)]
  apply Finset.sum_congr rfl
  intro e _
  change (if i = e.val.1 ∨ i = e.val.2 then w (edgeEquiv f e) else 0) =
    if f i = f e.val.1 ∨ f i = f e.val.2 then w (edgeEquiv f e) else 0
  simp only [f.injective.eq_iff]

private theorem degreeVariation_reindex (f : α ≃o β) (p : Edge β → Set.Icc (0 : ℝ) 1) :
    degreeVariation (p ∘ edgeEquiv f) = degreeVariation p := by
  classical
  have hd (i : α) : degreeSum (fun e ↦ ((p ∘ edgeEquiv f) e : ℝ)) i =
      degreeSum (fun e ↦ (p e : ℝ)) (f i) :=
    degreeSum_reindex f (fun e ↦ (p e : ℝ)) i
  unfold degreeVariation vertexMean
  simp_rw [hd]
  have hsum : (∑ i : α, degreeSum (fun e ↦ (p e : ℝ)) (f i)) =
      ∑ i : β, degreeSum (fun e ↦ (p e : ℝ)) i :=
    f.toEquiv.sum_comp (fun i ↦ degreeSum (fun e ↦ (p e : ℝ)) i)
  rw [hsum, Fintype.card_congr f.toEquiv]
  exact f.toEquiv.sum_comp (fun i : β ↦
    (degreeSum (fun e ↦ (p e : ℝ)) i -
      (∑ j : β, degreeSum (fun e ↦ (p e : ℝ)) j) / (Fintype.card β : ℝ)) ^ 2)

private theorem probability_regular_reindex (f : α ≃o β) (p : Edge β → Set.Icc (0 : ℝ) 1) :
    (graphLaw (p ∘ edgeEquiv f)).real regularEvent = (graphLaw p).real regularEvent := by
  classical
  let e := MeasurableEquiv.piCongrLeft (fun _ : Edge β ↦ ℝ) (edgeEquiv f)
  have hmap : MeasurePreserving e (graphLaw (p ∘ edgeEquiv f)) (graphLaw p) :=
    measurePreserving_piCongrLeft (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (p i)) (edgeEquiv f)
  have hpre : e.symm ⁻¹' (regularEvent : Set (Edge α → ℝ)) = regularEvent := by
    ext w
    change (∀ i j, degreeSum (w ∘ edgeEquiv f) i = degreeSum (w ∘ edgeEquiv f) j) ↔
      ∀ i j, degreeSum w i = degreeSum w j
    simp_rw [degreeSum_reindex f w]
    constructor
    · intro h i j
      simpa using h (f.symm i) (f.symm j)
    · intro h i j
      exact h (f i) (f j)
  rw [measureReal_def, measureReal_def, ← (hmap.symm e).measure_preimage
    measurableSet_regularEvent.nullMeasurableSet, hpre]

/-- Proposition 8.1 on an arbitrary finite ordered vertex set. -/
theorem probability_regular_le_variation_gaussian_finite (ξ : ℝ)
    (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {β : Type*} [Fintype β] [LinearOrder β],
      3 ≤ Fintype.card β → ∀ (p : Edge β → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) →
      (graphLaw p).real regularEvent ≤
        (C / Real.sqrt (Fintype.card β)) ^ Fintype.card β *
          Real.exp (-2 * degreeVariation p / ((Fintype.card β : ℝ) - 2)) := by
  obtain ⟨C, hC, hfin⟩ := probability_regular_le_variation_gaussian ξ hξ hξ'
  refine ⟨C, hC, ?_⟩
  intro b _ _ hb p hp
  let f := Fintype.orderIsoFinOfCardEq b (rfl : Fintype.card b = Fintype.card b)
  have h := hfin _ hb (p ∘ edgeEquiv f) (fun e ↦ hp (edgeEquiv f e))
  rwa [probability_regular_reindex f p, degreeVariation_reindex f p] at h

theorem exp_pow_le_factorial (k : ℕ) (hk : 0 < k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * k) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).2
    have hs := mul_le_mul hπ hk' (by norm_num : (0 : ℝ) ≤ 1) Real.pi_pos.le
    norm_num at hs ⊢
    linarith
  exact (le_mul_of_one_le_left (by positivity) hs).trans (Stirling.le_factorial_stirling k)

private theorem choose_le_exp_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
  have hfac := exp_pow_le_factorial k hk
  calc
    _ ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
    _ ≤ (n : ℝ) ^ k / ((k : ℝ) / Real.exp 1) ^ k :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = _ := by rw [← div_pow, div_div_eq_mul_div, mul_comm (n : ℝ)]

/-- Pointwise tail bound after summing Proposition 8.1 over the subsets of one order. -/
theorem probability_exact_order_le_pow (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} [Fintype α] [LinearOrder α]
      (p : Edge α → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ k : ℕ, 3 ≤ k →
        (graphLaw p).real (exactOrderEvent k) ≤
          (C * Fintype.card α / ((k : ℝ) * Real.sqrt k)) ^ k := by
  obtain ⟨B, hB, hfinite⟩ := probability_regular_le_variation_gaussian_finite ξ hξ hξ'
  refine ⟨B * Real.exp 1, by positivity, ?_⟩
  intro a _ _ p hp k hk
  classical
  let T := {S : Finset a // S.card = k}
  have hd (S : T) : (graphLaw p).real (inducedRegularEvent S.val) ≤
      (B / Real.sqrt k) ^ k := by
    rw [probability_induced_regular_eq]
    have hc : Fintype.card ↥S.val = k := (Fintype.card_coe S.val).trans S.property
    have h := hfinite (by rwa [hc]) (induce S.val p) (fun e ↦ hp (inducedEdge S.val e))
    rw [hc] at h
    refine h.trans (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_))
    unfold degreeVariation
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (by norm_num) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)) (by linarith)
  calc
    _ ≤ ∑ S : T, (graphLaw p).real (inducedRegularEvent S.val) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : T, (B / Real.sqrt k) ^ k := Finset.sum_le_sum (fun S _ ↦ hd S)
    _ = ((Fintype.card a).choose k : ℝ) * (B / Real.sqrt k) ^ k := by
      rw [Finset.sum_const, Finset.card_univ, card_fixed_order, nsmul_eq_mul]
    _ ≤ (Real.exp 1 * Fintype.card a / k) ^ k * (B / Real.sqrt k) ^ k :=
      mul_le_mul_of_nonneg_right (choose_le_exp_pow _ _ (by omega)) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem atLeastOrderEvent_eq_iUnion_exactOrderEvent (k : ℕ) :
    (atLeastOrderEvent k : Set (Edge α → ℝ)) =
      ⋃ l ∈ Finset.Icc k (Fintype.card α), exactOrderEvent l := by
  classical
  ext w
  simp only [atLeastOrderEvent, exactOrderEvent, Set.mem_iUnion, Finset.mem_Icc, Subtype.exists]
  constructor
  · rintro ⟨S, hS, hw⟩
    exact ⟨S.card, ⟨hS, Finset.card_le_univ S⟩, S, rfl, hw⟩
  · rintro ⟨l, hl, S, hS, hw⟩
    exact ⟨S, hS ▸ hl.1, hw⟩

/-- The Section 8 union bound, with the contribution of each larger order explicit. -/
theorem probability_at_least_order_le_sum_pow (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} [Fintype α] [LinearOrder α]
      (p : Edge α → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ k : ℕ, 3 ≤ k →
        (graphLaw p).real (atLeastOrderEvent k) ≤
          ∑ l ∈ Finset.Icc k (Fintype.card α),
            (C * Fintype.card α / ((l : ℝ) * Real.sqrt l)) ^ l := by
  obtain ⟨C, hC, h⟩ := probability_exact_order_le_pow ξ hξ hξ'
  refine ⟨C, hC, ?_⟩
  intro a _ _ p hp k hk
  rw [atLeastOrderEvent_eq_iUnion_exactOrderEvent]
  exact (measureReal_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum (fun l hl ↦ h p hp l (hk.trans (Finset.mem_Icc.mp hl).1)))

/-- The geometric upper tail at and above the paper's order-(n^{2/3}) scale. -/
theorem probability_at_least_order_le_geometric (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} [Fintype α] [LinearOrder α]
      (p : Edge α → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ k : ℕ, 3 ≤ k →
      2 * C * Fintype.card α ≤ (k : ℝ) * Real.sqrt k →
      (graphLaw p).real (atLeastOrderEvent k) ≤ 2 * (1 / 2 : ℝ) ^ k := by
  obtain ⟨C, hC, h⟩ := probability_at_least_order_le_sum_pow ξ hξ hξ'
  refine ⟨C, hC, ?_⟩
  intro a _ _ p hp k hk hcut
  have hb (l : ℕ) (hl : l ∈ Finset.Icc k (Fintype.card a)) :
      (C * Fintype.card a / ((l : ℝ) * Real.sqrt l)) ^ l ≤ (1 / 2 : ℝ) ^ l := by
    have hkl : (k : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
    have hl' : (0 : ℝ) < l := by
      have h' := hk.trans (Finset.mem_Icc.mp hl).1
      exact_mod_cast (show 0 < l by omega)
    have hmono : (k : ℝ) * Real.sqrt k ≤ (l : ℝ) * Real.sqrt l :=
      mul_le_mul hkl (Real.sqrt_le_sqrt hkl) (Real.sqrt_nonneg _) hl'.le
    apply pow_le_pow_left₀ (by positivity) _ _
    apply (div_le_iff₀ (mul_pos hl' (Real.sqrt_pos.2 hl'))).mpr
    linarith only [hcut.trans hmono]
  refine (h p hp k hk).trans ((Finset.sum_le_sum hb).trans ?_)
  rw [← Finset.Ico_succ_right_eq_Icc]
  calc
    _ ≤ (1 / 2 : ℝ) ^ k / (1 - 1 / 2) :=
      geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = _ := by ring


end BoundedEdgeRegularSubgraphs
