/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import SupportQuantization
public import MinimumShareStability

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem uniform_prefix_error_lower {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ) (r : ℝ) :
    r^2/12*(1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2) ≤
      prefixError q (uniformTarget m r) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hs := sparse_cumulative_quantization q m (r/(m : ℝ))
  have heq : (∑ l : Fin m, (prefixMass q l.val-(r/(m : ℝ))*(l.val : ℝ))^2) =
      ∑ l : Fin m, (prefixMass q l.val-prefixMass (uniformTarget m r) l.val)^2 := by
    apply Finset.sum_congr rfl
    intro l _
    rw [uniform_prefix_mass]
    ring
  rw [heq] at hs
  have halg : ((r/(m : ℝ))^2/12*((m : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2-(m : ℝ)))/(m : ℝ) =
      r^2/12*(1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2) := by
    field_simp
  rw [← halg]
  exact div_le_div_of_nonneg_right hs (le_of_lt hmR)

theorem uniform_prefix_mass_le (m : ℕ) (hm : 0 < m) (r : ℝ) (l : ℕ) (hl : l ≤ m) :
    prefixMass (uniformTarget m r) l = (l : ℝ)*(r/(m : ℝ)) := by
  by_cases he : l=m
  · subst l
    rw [prefixMass_full, uniformTarget_mass m hm r]
    field_simp
  · exact uniform_prefix_mass m r ⟨l,by omega⟩

theorem uniform_full_prefix_error_lower {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ) (r : ℝ)
    (hmass : ∑ j, q j = r) :
    r^2/(12*(m : ℝ)^3)*(((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1)) ≤
      prefixError q (uniformTarget m r) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hs := sparse_cumulative_quantization q (m+1) (r/(m : ℝ))
  have heq : (∑ l : Fin (m+1), (prefixMass q l.val-(r/(m : ℝ))*(l.val : ℝ))^2) =
      ∑ l : Fin m, (prefixMass q l.val-prefixMass (uniformTarget m r) l.val)^2 := by
    rw [Fin.sum_univ_castSucc]
    have hend : prefixMass q m-(r/(m : ℝ))*(m : ℝ) = 0 := by
      rw [prefixMass_full, hmass]
      field_simp
      ring
    simp only [Fin.val_last, hend, zero_pow (by norm_num : 2 ≠ 0), add_zero, Fin.val_castSucc]
    apply Finset.sum_congr rfl
    intro l _
    rw [uniform_prefix_mass]
    ring
  rw [heq] at hs
  have halg : ((r/(m : ℝ))^2/12*(((m+1 : ℕ) : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m+1 : ℕ) : ℝ)))/(m : ℝ) =
      r^2/(12*(m : ℝ)^3)*(((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1)) := by
    push_cast
    field_simp
  rw [← halg]
  exact div_le_div_of_nonneg_right hs (le_of_lt hmR)

/-- The full quantitative support lower bound for the uniform observed
    game, specialized to the paper's p=3/4, r=1/4 constants. -/
theorem uniform_fixed_share_support_lower {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqm : ∑ j, q j = 1/(4 : ℕ))
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ z) :
    (((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(304*(m : ℝ)^3) ≤ z := by
  norm_num only [Nat.cast_ofNat] at *
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hlower := uniform_full_prefix_error_lower hm q (1/4) hqm
  have hupper := two_anchor_fixed_share_stability hm (uniformTarget m (1/4)) q hq hqm
    (uniformTarget_mass m hm (1/4)) B hB hb z hz hresp
  have hsmall : (((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(192*(m : ℝ)^3) ≤
      prefixError q (uniformTarget m (1/4)) := by convert hlower using 1; ring
  calc
    _ = ((((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(192*(m : ℝ)^3))/(19/12) := by
      field_simp
      ring
    _ ≤ prefixError q (uniformTarget m (1/4))/(19/12) :=
      div_le_div_of_nonneg_right hsmall (by norm_num)
    _ ≤ z := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19/12)).mpr (by nlinarith)

/-- The variable-mass support obstruction under the two minimum shares. -/
theorem uniform_minimum_share_support_lower {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (a : Fin 2 → ℝ) (hq : ∀ j, 0 ≤ q j) (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ z) :
    (1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/304 ≤ z := by
  norm_num only [Nat.cast_ofNat] at *
  have hlower := uniform_prefix_error_lower hm q (1/4)
  have hupper := two_anchor_minimum_share_stability hm (uniformTarget m (1/4)) q a
    (fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j))
    (uniformTarget_mass m hm (1/4)) ha hq hnorm B hB hb z hz hresp
  have hsmall : (1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/192 ≤
      prefixError q (uniformTarget m (1/4)) := by convert hlower using 1; ring
  calc
    _ = ((1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/192)/(19/12) := by ring
    _ ≤ prefixError q (uniformTarget m (1/4))/(19/12) :=
      div_le_div_of_nonneg_right hsmall (by norm_num)
    _ ≤ z := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19/12)).mpr (by nlinarith)

theorem fixed_rate_simplification (m H : ℕ) (hm : 0 < m) (hdim : 2*H+1 ≤ m) :
    3/(1216*((H+1 : ℕ) : ℝ)^2) ≤
      (((m : ℝ)+1)^3/((H+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(304*(m : ℝ)^3) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
  have hdimR : 2*((H+1 : ℕ) : ℝ) ≤ (m : ℝ)+1 := by exact_mod_cast (show 2*(H+1) ≤ m+1 by omega)
  have hgap : 0 ≤ ((m : ℝ)+1)*(((m : ℝ)+1)-2*((H+1 : ℕ) : ℝ))*(((m : ℝ)+1)+2*((H+1 : ℕ) : ℝ)) := by
    positivity
  have hcubes : (m : ℝ)^3 ≤ ((m : ℝ)+1)^3 := by gcongr; linarith
  have hscaled : 3*(m : ℝ)^3 ≤ 4*(((m : ℝ)+1)^3-((m : ℝ)+1)*((H+1 : ℕ) : ℝ)^2) := by
    nlinarith
  have hbracket : 3*(m : ℝ)^3/(4*((H+1 : ℕ) : ℝ)^2) ≤
      ((m : ℝ)+1)^3/((H+1 : ℕ) : ℝ)^2-((m : ℝ)+1) := by
    apply (div_le_iff₀ (show 0 < 4*((H+1 : ℕ) : ℝ)^2 by positivity)).mpr
    have heq : (((m : ℝ)+1)^3/((H+1 : ℕ) : ℝ)^2-((m : ℝ)+1))*(4*((H+1 : ℕ) : ℝ)^2) =
        4*(((m : ℝ)+1)^3-((m : ℝ)+1)*((H+1 : ℕ) : ℝ)^2) := by
      field_simp
    rw [heq]
    exact hscaled
  calc
    _ = (3*(m : ℝ)^3/(4*((H+1 : ℕ) : ℝ)^2))/(304*(m : ℝ)^3) := by
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hbracket (by positivity)

theorem minimum_rate_simplification (m H : ℕ) (hm : 0 < m) (hdim : 2*(H+1) ≤ m) :
    3/(1216*((H+1 : ℕ) : ℝ)^2) ≤
      (1/((H+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/304 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
  have hdimR : 2*((H+1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdim
  have hpow : 4*((H+1 : ℕ) : ℝ)^2 ≤ (m : ℝ)^2 := by nlinarith
  have hinv : 1/(m : ℝ)^2 ≤ 1/(4*((H+1 : ℕ) : ℝ)^2) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have heq : 1/(4*((H+1 : ℕ) : ℝ)^2) = (1/((H+1 : ℕ) : ℝ)^2)/4 := by ring
  rw [heq] at hinv
  have hconst : 3/(1216*((H+1 : ℕ) : ℝ)^2) = ((1/((H+1 : ℕ) : ℝ)^2)*3/4)/304 := by ring
  rw [hconst]
  nlinarith

theorem uniform_fixed_share_inverse_square {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqm : ∑ j, q j = 1/(4 : ℕ))
    (hdim : 2*supportSize q+1 ≤ m)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ z) :
    3/(1216*((supportSize q+1 : ℕ) : ℝ)^2) ≤ z :=
  le_trans (fixed_rate_simplification m (supportSize q) hm hdim)
    (uniform_fixed_share_support_lower hm q hq hqm B hB hb z hz hresp)

theorem uniform_minimum_share_inverse_square {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (a : Fin 2 → ℝ) (hq : ∀ j, 0 ≤ q j) (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1) (hdim : 2*(supportSize q+1) ≤ m)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ z) :
    3/(1216*((supportSize q+1 : ℕ) : ℝ)^2) ≤ z :=
  le_trans (minimum_rate_simplification m (supportSize q) hm hdim)
    (uniform_minimum_share_support_lower hm q a hq ha hnorm B hB hb z hz hresp)

/-- A witness-wise total support obstruction, valid for every positive
    tolerance and every completion under the two minimum shares. -/
theorem uniform_total_support_lower {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (a : Fin 2 → ℝ) (hq : ∀ j, 0 ≤ q j) (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (ε : ℝ) (hε : 0 < ε)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ ε) :
    Real.sqrt (3/1216)*min ((m : ℝ)+2) (1/Real.sqrt ε) ≤ (supportSize q : ℝ)+2 := by
  norm_num only [Nat.cast_ofNat] at *
  let H := supportSize q
  have hrootε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hC : (Real.sqrt (3/1216))^2 = (3/1216 : ℝ) := Real.sq_sqrt (by norm_num)
  have hC0 : 0 ≤ Real.sqrt (3/1216) := Real.sqrt_nonneg _
  have hChalf : Real.sqrt (3/1216) ≤ 1/2 := by nlinarith
  by_cases hdim : 2*(H+1) ≤ m
  · have hbound := uniform_minimum_share_inverse_square hm q a hq ha hnorm hdim B hB hb ε (le_of_lt hε) hresp
    have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
    have hc : (3/1216 : ℝ) ≤ ε*((H+1 : ℕ) : ℝ)^2 := by
      have hh := (div_le_iff₀ (show 0 < 1216*((H+1 : ℕ) : ℝ)^2 by positivity)).mp hbound
      nlinarith
    have hsq : (Real.sqrt ε*((H+1 : ℕ) : ℝ))^2 = ε*((H+1 : ℕ) : ℝ)^2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hε)]
    have hs : Real.sqrt (3/1216) ≤ Real.sqrt ε*((H+1 : ℕ) : ℝ) := by
      have hnonneg := mul_nonneg (le_of_lt hrootε) (le_of_lt hN)
      nlinarith
    have hdiv : Real.sqrt (3/1216)/Real.sqrt ε ≤ ((H+1 : ℕ) : ℝ) :=
      (div_le_iff₀ hrootε).mpr (by nlinarith)
    calc
      _ ≤ Real.sqrt (3/1216)*(1/Real.sqrt ε) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
      _ = Real.sqrt (3/1216)/Real.sqrt ε := by ring
      _ ≤ ((H+1 : ℕ) : ℝ) := hdiv
      _ ≤ _ := by dsimp [H]; push_cast; linarith
  · have hdimR : (m : ℝ)+2 ≤ 2*((H : ℝ)+2) := by exact_mod_cast (show m+2 ≤ 2*(H+2) by omega)
    calc
      _ ≤ Real.sqrt (3/1216)*((m : ℝ)+2) := mul_le_mul_of_nonneg_left (min_le_left _ _) hC0
      _ ≤ (1/2)*((m : ℝ)+2) := mul_le_mul_of_nonneg_right hChalf (by positivity)
      _ ≤ _ := by dsimp [H] at hdimR; linarith

end
end SparseCompletion
