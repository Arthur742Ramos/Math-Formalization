/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.SupportLowerBound
public import ProtectedSources.PaperWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem supportSize_le_dimension {m : ℕ} (q : Fin m → ℝ) : supportSize q ≤ m := by
  classical
  unfold supportSize residualSupport
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => q j ≠ 0)

theorem two_anchor_total_support_card {m : ℕ} (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (ha : ∀ h, 0 < a h) :
    (Finset.univ.filter fun v => blockWeights a q v ≠ 0).card = supportSize q+2 := by
  classical
  rw [block_support_card]
  have heq : (Finset.univ.filter fun h => a h ≠ 0) = Finset.univ := by
    ext h
    simp [ne_of_gt (ha h)]
  rw [heq]
  simp only [Finset.card_univ, Fintype.card_fin, supportSize, residualSupport]
  omega

theorem uniform_grid_support_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2+gridSize 1 (1/4) ε : ℕ) : ℝ) ≤ 3/Real.sqrt ε := by
  have hr : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hr1 : Real.sqrt ε ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hε1
  have hquarter : Real.sqrt (1/4 : ℝ) = 1/2 := by norm_num
  have hroot : Real.sqrt (1*(1/4)/ε) = 1/(2*Real.sqrt ε) := by
    rw [one_mul, Real.sqrt_div (by norm_num), hquarter]
    ring
  by_cases he : 1/4 ≤ ε
  · have hrhalf : 1/2 ≤ Real.sqrt ε := by
      have hh := Real.sqrt_le_sqrt he
      rw [hquarter] at hh
      exact hh
    have hceil : gridSize 1 (1/4) ε ≤ 1 := by
      unfold gridSize
      apply Nat.ceil_le.mpr
      rw [hroot]
      apply (div_le_iff₀ (show 0 < 2*Real.sqrt ε by positivity)).mpr
      norm_num
      linarith
    have hc : ((2+gridSize 1 (1/4) ε : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show 2+gridSize 1 (1/4) ε ≤ 3 by omega)
    exact le_trans hc ((le_div_iff₀ hr).mpr (by nlinarith))
  · have hlt : ε < 1/4 := lt_of_not_ge he
    have hrhalf : Real.sqrt ε < 1/2 := by
      have hh := Real.sqrt_lt_sqrt (le_of_lt hε) hlt
      rw [hquarter] at hh
      exact hh
    have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (1*(1/4)/ε))
    change (gridSize 1 (1/4) ε : ℝ) < Real.sqrt (1*(1/4)/ε)+1 at hc
    rw [hroot] at hc
    have hm := mul_lt_mul_of_pos_right hc hr
    have hid : (1/(2*Real.sqrt ε))*Real.sqrt ε = 1/2 := by field_simp
    rw [add_mul, hid] at hm
    apply (le_div_iff₀ hr).mpr
    push_cast
    nlinarith

/-- Matching existential support rate obtained directly from the main
    sparse-witness theorem. It does not assert the paper's explicit bin
    constructions or their exact exploitability formulas. -/
theorem uniform_sparse_upper_rate {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1/(4 : ℕ)) ∧
      IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      (∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ ε) ∧
      (supportSize q : ℝ) ≤ 3*min (m : ℝ) (1/Real.sqrt ε) ∧
      (supportSize q : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt ε) := by
  norm_num only [Nat.cast_ofNat] at *
  let qstar := uniformTarget m (1/4)
  let K := rigidityCore qstar
  let D := rigidityCross qstar
  let p := twoShares (3/4)
  have hqstar : ∀ j, 0 ≤ qstar j := fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j)
  have hmass : ∑ j, qstar j = 1/4 := uniformTarget_mass m hm (1/4)
  have hresp0 : ∀ v, response (blockMatrix K D (orderedBlock 1)) (blockWeights p qstar) v ≤ 0 :=
    fun v => le_of_eq (two_anchor_target_feasible qstar (3/4) (1/4) (by norm_num) hmass v)
  obtain ⟨q,B,hq,hqm,_,hc,_,hB,hb,hresp⟩ := exact_game_sparse_completion 2 K D (orderedBlock 1)
    p qstar 1 (1/4) ε (by norm_num) (by norm_num) hε
    (fun _ => by norm_num [p,twoShares]) hqstar hmass (twoCore_skew _) (orderedBlock_skew 1)
    (orderedBlock_bounds 1 (by norm_num)) hresp0
  have hsupp : supportSize q ≤ 2+gridSize 1 (1/4) ε := by
    simpa only [supportSize,residualSupport] using hc
  have hdim : (supportSize q : ℝ) ≤ m := by exact_mod_cast supportSize_le_dimension q
  have hcard : (supportSize q : ℝ) ≤ 3/Real.sqrt ε :=
    le_trans (by exact_mod_cast hsupp) (uniform_grid_support_upper ε hε hε1)
  have hcard' : (supportSize q : ℝ) ≤ 3*(1/Real.sqrt ε) := by
    calc
      _ ≤ 3/Real.sqrt ε := hcard
      _ = _ := by ring
  have hr : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hr1 : Real.sqrt ε ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hε1
  have hresidual : (supportSize q : ℝ) ≤ 3*min (m : ℝ) (1/Real.sqrt ε) := by
    rcases le_total (m : ℝ) (1/Real.sqrt ε) with hh | hh
    · rw [min_eq_left hh]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    · rw [min_eq_right hh]
      nlinarith
  have htotal : (supportSize q : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt ε) := by
    rcases le_total ((m : ℝ)+2) (1/Real.sqrt ε) with hh | hh
    · rw [min_eq_left hh]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    · rw [min_eq_right hh]
      have hinv : 1 ≤ 1/Real.sqrt ε := (le_div_iff₀ hr).mpr (by nlinarith)
      nlinarith
  refine ⟨q,B,hq,hqm,hB,hb,?_,hresidual,htotal⟩
  simpa only [zero_add] using hresp

end
end SparseCompletion
