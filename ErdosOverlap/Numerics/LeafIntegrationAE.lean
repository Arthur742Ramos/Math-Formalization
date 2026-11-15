/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.LeafIntegration

/-!
# Almost-everywhere semantics of polynomial integration leaves

Compressed affine pieces may contain discarded periodic-grid endpoints.
All estimates here therefore permit exceptional null sets inside a leaf,
not only at its two endpoints. The exact polynomial primitive is unchanged.
The conjugate theorem also permits a piecewise witness derivative to equal
its leaf slope only almost everywhere.
-/

@[expose] public section

namespace ErdosOverlap.Numerics

open MeasureTheory Set

/-- Reflecting a null exceptional set preserves nullity. This transports an
affine-piece identity for `Q(x)` to the leaf identity for `Q(c-t)`. -/
theorem ae_Ioo_comp_sub_left {P : ℝ → Prop} {l r : ℝ}
    (hP : ∀ᵐ t ∂volume.restrict (Ioo l r), P t) (c : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo (c-r) (c-l)), P (c-t) := by
  have hglobal := ae_imp_of_ae_restrict hP
  have hpull := (volume.measurePreserving_sub_left c).quasiMeasurePreserving.ae hglobal
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hpull] with t ht hmem
  apply ht
  exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩

theorem integral_mono_ae_Ioo {f g : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hg : IntervalIntegrable g volume l r)
    (hpoint : ∀ᵐ t ∂volume.restrict (Ioo l r), f t ≤ g t) :
    (∫ t in l..r, f t) ≤ ∫ t in l..r, g t := by
  simp only [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_ae_restrict
    (hf.1.mono Ioo_subset_Ioc_self le_rfl)
    (hg.1.mono Ioo_subset_Ioc_self le_rfl) hpoint

theorem integral_lower_of_ae_margin {f g : ℝ → ℝ} {l r margin : ℝ}
    (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hg : IntervalIntegrable g volume l r)
    (hpoint : ∀ᵐ t ∂volume.restrict (Ioo l r), g t - margin ≤ f t) :
    (∫ t in l..r, g t) - margin*(r-l) ≤ ∫ t in l..r, f t := by
  have hc : IntervalIntegrable (fun _ : ℝ => margin) volume l r := intervalIntegrable_const
  have hm := integral_mono_ae_Ioo hlr (hg.sub hc) hf hpoint
  rw [intervalIntegral.integral_sub hg hc, intervalIntegral.integral_const] at hm
  convert hm using 1
  simp only [smul_eq_mul]
  ring

theorem integral_upper_of_ae_margin {f g : ℝ → ℝ} {l r margin : ℝ}
    (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hg : IntervalIntegrable g volume l r)
    (hpoint : ∀ᵐ t ∂volume.restrict (Ioo l r), f t ≤ g t + margin) :
    (∫ t in l..r, f t) ≤ (∫ t in l..r, g t) + margin*(r-l) := by
  have hc : IntervalIntegrable (fun _ : ℝ => margin) volume l r := intervalIntegrable_const
  have hm := integral_mono_ae_Ioo hlr hf (hg.add hc) hpoint
  rw [intervalIntegral.integral_add hg hc, intervalIntegral.integral_const] at hm
  convert hm using 1
  simp only [smul_eq_mul]
  ring

theorem leafPolynomial_integral_lower_bound_ae {f : ℝ → ℝ}
    (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r margin : ℚ)
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) (hlr : l ≤ r)
    (hf : IntervalIntegrable f volume (l : ℝ) (r : ℝ))
    (hpoint : ∀ᵐ t ∂volume.restrict (Ioo (l : ℝ) (r : ℝ)),
      leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 t - (margin : ℝ) ≤ f t) :
    ((leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
      alphaA betaA alphaB betaB alpha0 beta0 l r - margin*(r-l) : ℚ) : ℝ) ≤
      ∫ t in (l : ℝ)..(r : ℝ), f t := by
  have hi := (leafPolynomialMinorant_continuous csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0).intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have hm := integral_lower_of_ae_margin (by exact_mod_cast hlr) hf hi hpoint
  rw [integral_leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0 l r hrA hrB] at hm
  simpa only [Rat.cast_sub, Rat.cast_mul] using hm

theorem leafPolynomial_integral_upper_bound_ae {f : ℝ → ℝ}
    (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r margin : ℚ)
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) (hlr : l ≤ r)
    (hf : IntervalIntegrable f volume (l : ℝ) (r : ℝ))
    (hpoint : ∀ᵐ t ∂volume.restrict (Ioo (l : ℝ) (r : ℝ)),
      f t ≤ leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 t + (margin : ℝ)) :
    (∫ t in (l : ℝ)..(r : ℝ), f t) ≤
      ((leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 l r + margin*(r-l) : ℚ) : ℝ) := by
  have hi := (leafPolynomialMinorant_continuous csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0).intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have hm := integral_upper_of_ae_margin (by exact_mod_cast hlr) hf hi hpoint
  rw [integral_leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0 l r hrA hrB] at hm
  simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul] using hm

theorem conjugate_polynomial_leaf_lower_bound_ae
    {A B L U K V actualLam : ℝ → ℝ}
    (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r delta : ℚ)
    {lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ : ℝ}
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) (hlr : l ≤ r) (hdelta : 0 ≤ delta)
    (hf : IntervalIntegrable
      (fun t => profileConjugate (max (B t) 0) (|A t| + |B t|)
        (L t) (U t) (actualLam t)) volume (l : ℝ) (r : ℝ))
    (hL : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), 0 ≤ L t ∧ L t ≤ 1)
    (hU : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), 0 ≤ U t ∧ U t ≤ 1)
    (hK : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), K t = min (U t) (L t))
    (hV : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), V t = U t-K t)
    (hsA : -1 ≤ sA ∧ sA ≤ 1) (hsB : -1 ≤ sB ∧ sB ≤ 1)
    (hrho : 0 ≤ rho ∧ rho ≤ 1) (hsigma : 0 ≤ sigma ∧ sigma ≤ 1)
    (h₁ : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      max (|lam| - sA*normalizedPolynomialValue csA centerA radiusA t +
        sigma*normalizedPolynomialValue csB centerB radiusB t) 0 ≤
      alpha₁*(|lam| - sA*normalizedPolynomialValue csA centerA radiusA t +
        sigma*normalizedPolynomialValue csB centerB radiusB t) + beta₁)
    (h₂ : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      max (|lam| - sA*normalizedPolynomialValue csA centerA radiusA t -
        sB*normalizedPolynomialValue csB centerB radiusB t) 0 ≤
      alpha₂*(|lam| - sA*normalizedPolynomialValue csA centerA radiusA t -
        sB*normalizedPolynomialValue csB centerB radiusB t) + beta₂)
    (hA : ∀ᵐ t ∂volume.restrict (Ioo (l : ℝ) (r : ℝ)),
      |A t - normalizedPolynomialValue csA centerA radiusA t| ≤ (delta : ℝ))
    (hB : ∀ᵐ t ∂volume.restrict (Ioo (l : ℝ) (r : ℝ)),
      |B t - normalizedPolynomialValue csB centerB radiusB t| ≤ (delta : ℝ))
    (hlam : ∀ᵐ t ∂volume.restrict (Ioo (l : ℝ) (r : ℝ)), actualLam t = lam)
    (hweights : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 t =
      expandedMinorant (normalizedPolynomialValue csA centerA radiusA t)
        (normalizedPolynomialValue csB centerB radiusB t) (L t) (K t) (V t)
        lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂) :
    ((leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
      alphaA betaA alphaB betaB alpha0 beta0 l r - 2*delta*(r-l) : ℚ) : ℝ) ≤
      ∫ t in (l : ℝ)..(r : ℝ),
        profileConjugate (max (B t) 0) (|A t| + |B t|) (L t) (U t) (actualLam t) := by
  apply leafPolynomial_integral_lower_bound_ae csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0 l r (2*delta) hrA hrB hlr hf
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo, hA, hB, hlam] with t ht hAt hBt hlt
  rw [hlt, hweights t ht]
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  exact actual_conjugate_expanded_minorant (hL t ht) (hU t ht) (hK t ht) (hV t ht)
    hsA hsB hrho hsigma (h₁ t ht) (h₂ t ht) (by exact_mod_cast hdelta) hAt hBt

end ErdosOverlap.Numerics
