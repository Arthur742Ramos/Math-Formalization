module

public import BoundedEdgeRegularSubgraphs.Model
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem twice_sum_edges (f : α → α → ℝ)
    (hsym : ∀ i j, f i j = f j i) :
    2 * (∑ e : Edge α, f e.val.1 e.val.2) =
      (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  classical
  let F : α × α → ℝ := fun e ↦ f e.1 e.2
  let L : Finset (α × α) := Finset.univ.filter (fun e ↦ e.1 < e.2)
  let U : Finset (α × α) := Finset.univ.filter (fun e ↦ e.2 < e.1)
  let D : Finset (α × α) := Finset.univ.filter (fun e ↦ e.1 = e.2)
  have hlo : (∑ e : Edge α, F e.val) = ∑ e ∈ L, F e := by
    apply Finset.sum_bij (fun e _ ↦ e.val)
    · intro e _
      simpa [L] using e.property
    · exact fun _ _ _ _ h ↦ Subtype.ext h
    · intro e he
      refine ⟨⟨e, ?_⟩, Finset.mem_univ _, rfl⟩
      simpa [L] using he
    · intros
      rfl
  have hup : (∑ e ∈ L, F e) = ∑ e ∈ U, F e := by
    apply Finset.sum_bij (fun e _ ↦ e.swap)
    · simp [L, U]
    · intro e _ e' _ h
      simpa using congrArg Prod.swap h
    · intro e he
      refine ⟨e.swap, ?_, by simp⟩
      simpa [L, U] using he
    · intro e _
      exact hsym _ _
  have hd : (∑ e ∈ D, F e) = ∑ i, f i i := by
    symm
    apply Finset.sum_bij (fun i _ ↦ (i, i))
    · simp [D]
    · simp
    · rintro ⟨i, j⟩ hij
      simp only [D, Finset.mem_filter_univ] at hij
      subst j
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · simp [F]
  have hall : (∑ e, F e) = (∑ e ∈ L, F e) + (∑ e ∈ U, F e) + ∑ e ∈ D, F e := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e : α × α ↦ e.1 = e.2) F]
    have hdis : Disjoint L U := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact (lt_asymm (by simpa [L] using he)) (by simpa [U] using he')
    rw [← Finset.sum_union hdis]
    have hUnion : L ∪ U = Finset.univ.filter (fun e : α × α ↦ ¬ e.1 = e.2) := by
      ext e
      simp only [L, U, Finset.mem_union, Finset.mem_filter_univ]
      exact (ne_iff_lt_or_gt).symm
    rw [hUnion]
    exact add_comm _ _
  rw [Fintype.sum_prod_type] at hall
  change (∑ i, ∑ j, f i j) = _ at hall
  change 2 * (∑ e : Edge α, F e.val) = _
  rw [hlo, hall, ← hup, hd]
  ring

/-- The complete-graph quadratic identity used in the vertex tilt. -/
theorem sum_edge_squares (v : α → ℝ) :
    (∑ e : Edge α, (v e.val.1 + v e.val.2) ^ 2) =
      (Fintype.card α - 2 : ℝ) * ∑ i, (v i) ^ 2 + (∑ i, v i) ^ 2 := by
  have h := twice_sum_edges (fun i j ↦ (v i + v j) ^ 2)
    (fun i j ↦ by rw [add_comm])
  have hcross : (∑ i, (2 * v i) * ∑ j, v j) = 2 * (∑ i, v i) ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hrect : (∑ i, ∑ j, (v i + v j) ^ 2) =
      2 * (Fintype.card α : ℝ) * (∑ i, v i ^ 2) + 2 * (∑ i, v i) ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcross]
    ring
  have hdiag : (∑ i, (v i + v i) ^ 2) = 4 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [hrect, hdiag] at h
  linarith

/-- Pair a degree vector against vertex weights by summing over its edges. -/
theorem weighted_degree_sum (w : Edge α → ℝ) (v : α → ℝ) :
    (∑ i, v i * degreeSum w i) =
      ∑ e : Edge α, (v e.val.1 + v e.val.2) * w e := by
  simp_rw [degreeSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  simp_rw [mul_ite, mul_zero]
  have hsplit (i : α) :
      (if i = e.val.1 ∨ i = e.val.2 then v i * w e else 0) =
      (if i = e.val.1 then v i * w e else 0) +
        (if i = e.val.2 then v i * w e else 0) := by
    by_cases h : i = e.val.1
    · subst i
      simp [hne]
    · by_cases h' : i = e.val.2 <;> simp [h, h', hne.symm]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_mul]

omit [LinearOrder α] in
theorem sum_sub_vertexMean (u : α → ℝ) :
    ∑ i, (u i - vertexMean u) = 0 := by
  by_cases hn : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hne : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.sum_sub_distrib]
    simp [vertexMean, mul_div_cancel₀, hne]

/-- Almost every outcome is a 0-1 assignment on the unordered edges. -/
theorem graphLaw_ae_binary (p : Edge α → Set.Icc (0 : ℝ) 1) :
    ∀ᵐ w ∂graphLaw p, ∀ e, w e = 0 ∨ w e = 1 := by
  rw [ae_all_iff]
  intro e
  have hp := measurePreserving_eval (fun e ↦ bernoulliMeasure (1 : ℝ) 0 (p e)) e
  have h : ∀ᵐ x ∂bernoulliMeasure (1 : ℝ) 0 (p e), x = 0 ∨ x = 1 := by
    have hmeas : MeasurableSet ({0, 1} : Set ℝ) :=
      (measurableSet_singleton _).insert _
    apply ae_iff.mpr
    exact bernoulliMeasure_apply_of_notMem_of_notMem _ hmeas.compl (by simp) (by simp)
  exact hp.quasiMeasurePreserving.ae h

private theorem coordinate_ae_mem_Icc (p : Edge α → Set.Icc (0 : ℝ) 1) (e : Edge α) :
    ∀ᵐ w ∂graphLaw p, w e ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [graphLaw_ae_binary p] with w hw
  rcases hw e with h | h <;> simp [h]

private theorem coordinate_mean (p : Edge α → Set.Icc (0 : ℝ) 1) (e : Edge α) :
    ∫ w, w e ∂graphLaw p = (p e : ℝ) := by
  rw [graphLaw, integral_eval]
  simpa using integral_bernoulliMeasure (1 : ℝ) 0 (p e) id

/-- The mean of the degree in the sampled graph is the incident probability sum. -/
theorem integral_degreeSum (p : Edge α → Set.Icc (0 : ℝ) 1) (i : α) :
    ∫ w, degreeSum w i ∂graphLaw p = degreeSum (fun e ↦ (p e : ℝ)) i := by
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  unfold degreeSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _
    split_ifs
    · exact coordinate_mean p e
    · simp
  · intro e _
    split_ifs
    · exact Integrable.of_mem_Icc 0 1 (measurable_pi_apply e).aemeasurable
        (coordinate_ae_mem_Icc p e)
    · exact integrable_const _

/-- Proposition 9.1, with the degree variation computed on the given vertex set. -/
theorem probability_regular_le (p : Edge α → Set.Icc (0 : ℝ) 1)
    (hk : 3 ≤ Fintype.card α) :
    (graphLaw p).real regularEvent ≤
      Real.exp (-2 * degreeVariation p / (Fintype.card α - 2 : ℝ)) := by
  classical
  let P := graphLaw p
  have : IsProbabilityMeasure P := by dsimp [P, graphLaw]; infer_instance
  let u : α → ℝ := degreeSum (fun e ↦ (p e : ℝ))
  let v : α → ℝ := fun i ↦ u i - vertexMean u
  let V : ℝ := ∑ i, (v i) ^ 2
  change P.real regularEvent ≤ Real.exp (-2 * V / (Fintype.card α - 2 : ℝ))
  have hv : ∑ i, v i = 0 := sum_sub_vertexMean u
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))
  rcases hV.eq_or_lt with hzero | hpos
  · simp [← hzero, measureReal_le_one]
  let a : Edge α → ℝ := fun e ↦ v e.val.1 + v e.val.2
  let X : Edge α → (Edge α → ℝ) → ℝ :=
    fun e w ↦ a e * ((p e : ℝ) - w e)
  have hind : iIndepFun X P := by
    dsimp [X, P, graphLaw]
    exact iIndepFun_pi (fun e ↦ (show Measurable (fun x : ℝ ↦
      a e * ((p e : ℝ) - x)) by fun_prop).aemeasurable)
  let c : Edge α → NNReal := fun e ↦ ⟨(a e) ^ 2, sq_nonneg _⟩ * (1 / 2) ^ 2
  have hsub (e : Edge α) : HasSubgaussianMGF (X e) (c e) P := by
    have hm : AEMeasurable (fun w : Edge α → ℝ ↦ w e) P :=
      (measurable_pi_apply e).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc hm (coordinate_ae_mem_Icc p e)
    rw [coordinate_mean p e] at h
    have h' := h.neg.const_mul (a e)
    simpa [X, c, neg_sub, Pi.neg_apply] using h'
  have hregular : regularEvent ⊆ {w | V ≤ ∑ e, X e w} := by
    intro w hw
    have hc : ∀ i j, degreeSum w i = degreeSum w j := hw
    have hnonempty : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    let i₀ : α := Classical.choice hnonempty
    have hwzero : ∑ i, v i * degreeSum w i = 0 := by
      simp_rw [fun i ↦ hc i i₀]
      rw [← Finset.sum_mul, hv, zero_mul]
    have hmean : ∑ i, v i * u i = V := by
      have h (i : α) : v i * u i = v i ^ 2 + v i * vertexMean u := by
        dsimp [v]
        ring
      simp [h, Finset.sum_add_distrib, ← Finset.sum_mul, hv, V]
    change V ≤ ∑ e, X e w
    simp_rw [X, mul_sub, Finset.sum_sub_distrib]
    change V ≤ (∑ e : Edge α, (v e.val.1 + v e.val.2) * (p e : ℝ)) -
      (∑ e : Edge α, (v e.val.1 + v e.val.2) * w e)
    rw [← weighted_degree_sum, ← weighted_degree_sum, hwzero, sub_zero]
    exact hmean.ge
  have hc_sum : (↑(∑ e, c e) : ℝ) = (Fintype.card α - 2 : ℝ) * V / 4 := by
    rw [NNReal.coe_sum]
    change (∑ e : Edge α, (v e.val.1 + v e.val.2) ^ 2 * ((1 : ℝ) / 2) ^ 2) =
      (Fintype.card α - 2 : ℝ) * V / 4
    rw [← Finset.sum_mul, sum_edge_squares v, hv, zero_pow (by decide), add_zero]
    ring
  have hn : 0 < (Fintype.card α - 2 : ℝ) := by
    have : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hk
    linarith
  calc
    P.real regularEvent ≤ P.real {w | V ≤ ∑ e, X e w} :=
      measureReal_mono hregular
    _ ≤ Real.exp (-V ^ 2 / (2 * ↑(∑ e, c e))) :=
      HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (fun e _ ↦ hsub e) hV
    _ = Real.exp (-2 * V / (Fintype.card α - 2 : ℝ)) := by
      rw [hc_sum]
      congr 1
      field_simp
      ring

end BoundedEdgeRegularSubgraphs
