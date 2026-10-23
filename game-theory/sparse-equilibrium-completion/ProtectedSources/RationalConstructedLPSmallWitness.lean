/- AI-assisted formalization under repository Apache-2.0.
Small feasible rational points for the ACTUAL fixed-anchor
append and interval physical-repertoire LP constructors at their original
binders, with input-derived matrix heights and earned coordinate bounds.
This is separate from FM output height and polynomial solver time. -/
module
public import ProtectedSources.RationalLPSmallWitness
public import ProtectedSources.RationalRepertoireInputHeight
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_gap_append_exists_small_feasible_point
    {k m B BR : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m)
    (hK : ∀ a b, RationalInputHeight (K a b) B)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hR : ∀ row j, RationalInputHeight (R.coefficient row j) BR)
    (hb : ∀ row, RationalInputHeight (R.rightSide row) BR)
    (hf : ∃ x, ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x) :
    ∃ q, ((rationalGapSystem K D p M r ρ η).append R).Satisfies q ∧
      ∀ j, RationalInputHeight (q j)
        (rationalLPSmallWitnessHeight (2*m+2+k+rationalGridSize M r η+Fintype.card I) m
          (rationalFixedAnchorInputHeight k B+BR)) := by
  obtain ⟨hc,hs⟩ := rational_gap_append_repertoire_input_height
    K D p M r ρ η R hK hD hp hM hr hρ hη hR hb
  have hh := rational_lp_exists_small_feasible_point
    ((rationalGapSystem K D p M r ρ η).append R) hc hs (fun _ => |(r : ℝ)|)
    (fun x hx => rational_gap_append_real_coordinate_bound K D p M r ρ η R x hx) hf
  have hrows : Fintype.card (RationalGapRow k m (rationalGridSize M r η) ⊕ I) =
      2*m+2+k+rationalGridSize M r η+Fintype.card I := by
    rw [Fintype.card_sum, rational_gap_encoding_rows]
  simpa only [hrows] using hh

theorem rational_interval_repertoire_exists_small_feasible_point
    {k m B BR : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hlK : ∀ a b, RationalInputHeight (loK a b) B)
    (hhK : ∀ a b, RationalInputHeight (hiK a b) B)
    (hlo : ∀ i a, RationalInputHeight (lo i a) B)
    (hhi : ∀ i a, RationalInputHeight (hi i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hR : ∀ row j, RationalInputHeight (R.coefficient row j) BR)
    (hb : ∀ row, RationalInputHeight (R.rightSide row) BR)
    (hf : ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    let H := rationalGridSize M r η
    ∃ q, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies q ∧
      ∀ j, RationalInputHeight (q j)
        (rationalLPSmallWitnessHeight (rationalIntervalRowCount k m H+Fintype.card I)
          (rationalIntervalVariableCount k m H) (rationalIntervalRepertoireInputHeight k m B BR)) := by
  obtain ⟨hc,hs⟩ := rational_interval_repertoire_system_input_height
    loK hiK lo hi p M r ρ η R hlK hhK hlo hhi hp hM hr hρ hη hR hb
  have hh := rational_lp_exists_small_feasible_point
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) hc hs
    (rationalIntervalCoordinateRadius loK hiK lo hi M r η)
    (fun x hx => rational_interval_repertoire_coordinate_radius loK hiK lo hi p M r ρ η R x hx) hf
  simpa only [rational_interval_repertoire_row_count, rationalIntervalVariableCount] using hh

/-- Once the small packed point is earned, the literal recovery division
also has an explicit canonical height bound, including its zero-mass branch.
This does not assert a height for the output of the existing FM program. -/
theorem rational_interval_small_point_recovery_height {k m H B P : ℕ}
    (lo : Fin m → Fin k → ℚ) (x : Fin (m+(m*k+(k*k+H*m))) → ℚ)
    (hlo : ∀ i a, RationalInputHeight (lo i a) B)
    (hx : ∀ u, RationalInputHeight (x u) P) :
    ∀ i a, RationalInputHeight (rationalIntervalRecover lo (intervalV x) (intervalQ x) i a) (B+4*P) := by
  intro i a
  unfold rationalIntervalRecover
  split
  · exact rational_input_height_mono (hlo i a) (by omega)
  · exact rational_input_height_mono
      (rational_input_height_div
        (hx (rationalIntervalVariableEquiv k m H (.inr (.inl (i,a)))))
        (hx (rationalIntervalVariableEquiv k m H (.inl i)))) (by omega)

end SparseCompletion
