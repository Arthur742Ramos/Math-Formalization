/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.BalancedGame
public import ProtectedSources.CoreAdjustment

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem double_grid_support_upper (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (((2 : ℕ)+(2 : ℕ)*gridSize 1 (1/(4 : ℕ)) e : ℕ) : ℝ) ≤ (5 : ℕ)/Real.sqrt e := by
  norm_num only [Nat.cast_ofNat] at *
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hs1 : Real.sqrt e ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt he1
  have hroot : Real.sqrt (1*(1/4)/e) = 1/(2*Real.sqrt e) := by
    rw [one_mul,Real.sqrt_div (by norm_num)]
    norm_num
    ring
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (1*(1/4)/e))
  change (gridSize 1 (1/4) e : ℝ) < Real.sqrt (1*(1/4)/e)+1 at hc
  rw [hroot] at hc
  have hm := mul_lt_mul_of_pos_right hc hs
  have hid : (1/(2*Real.sqrt e))*Real.sqrt e=1/2 := by field_simp
  rw [add_mul,hid] at hm
  apply (le_div_iff₀ hs).mpr
  push_cast
  nlinarith

/-- A sparse central witness with its entire error in the two anchor
    responses, ready for the single-core uncertainty adjustment. -/
theorem uniform_binned_upper (m : ℕ) (hm : 0 < m) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      (supportSize q : ℝ)+(2 : ℕ) ≤ (5 : ℕ)*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt e) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧ d ≤ e ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  let H := gridSize 1 (1/4) e
  have hgrid := gridSize_bound 1 (1/4) e (by norm_num) (by norm_num) he
  have hH : 0 < H := by
    by_contra hh
    have hz : H=0 := by omega
    change 1*(1/4 : ℝ) ≤ e*(H : ℝ)^2 at hgrid
    rw [hz] at hgrid
    norm_num at hgrid
  have hr : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hr1 : Real.sqrt e ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt he1
  by_cases hdim : m ≤ H
  · let qstar := uniformTarget m (1/4)
    have hq : ∀ j, 0 ≤ qstar j := fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hmass : ∑ j, qstar j=1/4 := uniformTarget_mass m hm (1/4)
    have hresp := two_anchor_target_feasible qstar (3/4) (1/4) (by norm_num) hmass
    have hcard : (supportSize qstar : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt e) := by
      have hqcard : (supportSize qstar : ℝ) ≤ m := by exact_mod_cast supportSize_le_dimension qstar
      have hsmall : (supportSize qstar : ℝ)+2 ≤ 5/Real.sqrt e := by
        have hc : (supportSize qstar : ℝ)+2 ≤ ((2+2*H : ℕ) : ℝ) := by
          have hh := supportSize_le_dimension qstar
          exact_mod_cast (show supportSize qstar+2 ≤ 2+2*H by omega)
        exact le_trans hc (double_grid_support_upper e he he1)
      rcases le_total ((m : ℝ)+2) (1/Real.sqrt e) with hh | hh
      · rw [min_eq_left hh]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith
      · rw [min_eq_right hh]
        calc
          _ ≤ 5/Real.sqrt e := hsmall
          _ = _ := by ring
    refine ⟨qstar,orderedBlock 1,0,hq,hmass,orderedBlock_skew 1,
      orderedBlock_bounds 1 (by norm_num),hcard,le_refl 0,?_,le_of_lt he,?_,?_,?_⟩
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hq j)
        (exposingWeight_bounds hm qstar hq (1/4) hmass j).1
    · exact hresp _
    · simpa only [neg_zero,rigidityCore,rigidityCross,qstar,Nat.cast_ofNat] using hresp (.inl 1)
    · intro j
      exact le_of_eq (hresp (.inr j))
  · have hHm : H ≤ m := by omega
    obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,herr,h0,h1,hrows⟩ := balanced_game_witness m H hm hH hHm
    norm_num only [Nat.cast_ofNat] at herr
    have hdH : d ≤ e := by
      have hHR : (0 : ℝ) < H := Nat.cast_pos.mpr hH
      have heq : (1/16 : ℝ)/(3*(H : ℝ)^2)=1/(48*(H : ℝ)^2) := by ring
      rw [heq] at herr
      have hg : (1/4 : ℝ) ≤ e*(H : ℝ)^2 := by simpa only [one_mul] using hgrid
      have hbound : 1/(48*(H : ℝ)^2) ≤ e := by
        apply (div_le_iff₀ (show 0 < 48*(H : ℝ)^2 by positivity)).mpr
        nlinarith
      exact le_trans herr hbound
    have hdimq : (supportSize q : ℝ) ≤ m := by exact_mod_cast le_trans hcard (min_le_left _ _)
    have hcount : (supportSize q : ℝ)+2 ≤ 5/Real.sqrt e := by
      have hh : (supportSize q : ℝ)+2 ≤ ((2+2*H : ℕ) : ℝ) := by
        have hc := le_trans hcard (min_le_right _ _)
        exact_mod_cast (show supportSize q+2 ≤ 2+2*H by omega)
      exact le_trans hh (double_grid_support_upper e he he1)
    have htotal : (supportSize q : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt e) := by
      rcases le_total ((m : ℝ)+2) (1/Real.sqrt e) with hh | hh
      · rw [min_eq_left hh]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith
      · rw [min_eq_right hh]
        calc
          _ ≤ 5/Real.sqrt e := hcount
          _ = _ := by ring
    exact ⟨q,B,d,hq,hmass,hB,hb,htotal,hd,hβ,hdH,h0,h1,hrows⟩

theorem uniform_core_uncertainty_upper (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (he : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) (he1 : ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ ≤ 1) :
    ∃ (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ),
      UniformCoreWitness m ε δ q u B ∧
      (supportSize q : ℝ)+(2 : ℕ) ≤ (5 : ℕ)*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,hde,h0,h1,hrows⟩ :=
    uniform_binned_upper m hm (ε+(3/8)*δ) he he1
  obtain ⟨u,hu⟩ := uniform_core_adjust hm q B d ε δ hq hmass hB hb hd hβ hε hδ hde h0 h1 hrows
  exact ⟨q,u,B,hu,hcard⟩

end
end SparseCompletion
