/- AI-assisted formalization under repository Apache-2.0.
Actual fixed-anchor append and interval physical-variable repertoire lifting.
Repertoire coefficients/RHS have explicit canonical INPUT component bounds.
All bounds include the generated row/variable dimensions, including H. -/
module
public import ProtectedSources.RationalIntervalInputHeight
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalPhysicalRepertoireInputHeight (k m BR : ℕ) : ℕ :=
  rationalIntervalVariableCount k m 0 + 2*BR*(rationalIntervalVariableCount k m 0+1)

def rationalIntervalRepertoireInputHeight (k m B BR : ℕ) : ℕ :=
  rationalIntervalInputHeight k m B+rationalPhysicalRepertoireInputHeight k m BR+BR

theorem rational_interval_physical_form_input_height (k m H : ℕ)
    (j : Fin (m+(m*k+(k*k+0*m)))) (u : Fin (m+(m*k+(k*k+H*m)))) :
    RationalInputHeight (intervalPhysicalForm k m H j u) 0 :=
  rational_interval_basis_input_height _ u

theorem rational_interval_lifted_repertoire_coefficient_input_height {k m H BR : ℕ} {I : Type*}
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hR : ∀ row j, RationalInputHeight (R.coefficient row j) BR)
    (row : I) (u : Fin (m+(m*k+(k*k+H*m)))) :
    RationalInputHeight (rationalFormSum (fun j => rationalFormScale (R.coefficient row j)
      (intervalPhysicalForm k m H j)) u) (rationalPhysicalRepertoireInputHeight k m BR) := by
  apply rational_input_height_fin_sum
  intro j
  simpa only [Nat.add_zero, rationalFormScale] using rational_input_height_mul (hR row j)
    (rational_interval_physical_form_input_height k m H j u)

theorem rational_interval_repertoire_row_count (k m H : ℕ) (I : Type*) [Fintype I] :
    Fintype.card (RationalIntervalRows k m H ⊕ I) =
      rationalIntervalRowCount k m H+Fintype.card I := by
  rw [Fintype.card_sum, rational_interval_rows_exact_count]

theorem rational_interval_repertoire_system_input_height {k m B BR : ℕ} {I : Type*}
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
    (hb : ∀ row, RationalInputHeight (R.rightSide row) BR) :
    (∀ row u, RationalInputHeight
      ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).coefficient row u)
      (rationalIntervalRepertoireInputHeight k m B BR)) ∧
      ∀ row, RationalInputHeight
        ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).rightSide row)
        (rationalIntervalRepertoireInputHeight k m B BR) := by
  obtain ⟨hc, hs⟩ := rational_interval_system_input_height loK hiK lo hi p M r ρ η hlK hhK hlo hhi hp hM hr hρ hη
  constructor
  · rintro (row | row) u
    · exact rational_input_height_mono (hc row u)
        (by unfold rationalIntervalRepertoireInputHeight; omega)
    · exact rational_input_height_mono
        (rational_interval_lifted_repertoire_coefficient_input_height R hR row u)
        (by unfold rationalIntervalRepertoireInputHeight; omega)
  · rintro (row | row)
    · exact rational_input_height_mono (hs row)
        (by unfold rationalIntervalRepertoireInputHeight; omega)
    · exact rational_input_height_mono (hb row)
        (by unfold rationalIntervalRepertoireInputHeight; omega)

/-- Includes every arbitrary finite declared physical repertoire row at the
literal original binder, with its actual lift into the epigraph variables. -/
theorem rational_interval_repertoire_indexed_encoding_bits {k m B BR : ℕ} {I : Type*} [Fintype I]
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
    (hb : ∀ row, RationalInputHeight (R.rightSide row) BR) :
    let H := rationalGridSize M r η
    let rows := rationalIntervalRowCount k m H+Fintype.card I
    let vars := rationalIntervalVariableCount k m H
    rationalIndexedLinearSystemEncodingBits (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) ≤
      rows*(vars+1)*(2*rationalIntervalRepertoireInputHeight k m B BR+rows+vars+6) := by
  obtain ⟨hc, hs⟩ := rational_interval_repertoire_system_input_height
    loK hiK lo hi p M r ρ η R hlK hhK hlo hhi hp hM hr hρ hη hR hb
  have hh := rational_indexed_system_polynomial_encoding_bits_of_entry_bound
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) hc hs
  simpa only [rational_interval_repertoire_row_count, rationalIntervalVariableCount] using hh

theorem rational_gap_append_repertoire_input_height {k m B BR : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m)
    (hK : ∀ a b, RationalInputHeight (K a b) B)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hR : ∀ row j, RationalInputHeight (R.coefficient row j) BR)
    (hb : ∀ row, RationalInputHeight (R.rightSide row) BR) :
    (∀ row j, RationalInputHeight
      (((rationalGapSystem K D p M r ρ η).append R).coefficient row j)
      (rationalFixedAnchorInputHeight k B+BR)) ∧
      ∀ row, RationalInputHeight (((rationalGapSystem K D p M r ρ η).append R).rightSide row)
        (rationalFixedAnchorInputHeight k B+BR) := by
  obtain ⟨hc, hs⟩ := rational_gap_system_input_height K D p M r ρ η hK hD hp hM hr hρ hη
  exact rational_linear_append_input_height _ R hc hs hR hb

/-- The actual fixed-anchor LP passed to rationalGapSolve includes R here;
R has explicit input component bounds, not a supplied output budget. -/
theorem rational_gap_append_repertoire_indexed_encoding_bits {k m B BR : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m)
    (hK : ∀ a b, RationalInputHeight (K a b) B)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hR : ∀ row j, RationalInputHeight (R.coefficient row j) BR)
    (hb : ∀ row, RationalInputHeight (R.rightSide row) BR) :
    let rows := 2*m+2+k+rationalGridSize M r η+Fintype.card I
    rationalIndexedLinearSystemEncodingBits ((rationalGapSystem K D p M r ρ η).append R) ≤
      rows*(m+1)*(2*(rationalFixedAnchorInputHeight k B+BR)+rows+m+6) := by
  obtain ⟨hc, hs⟩ := rational_gap_append_repertoire_input_height K D p M r ρ η R hK hD hp hM hr hρ hη hR hb
  have hh := rational_indexed_system_polynomial_encoding_bits_of_entry_bound
    ((rationalGapSystem K D p M r ρ η).append R) hc hs
  rw [Fintype.card_sum, rational_gap_encoding_rows] at hh
  exact hh

theorem rational_interval_empty_variables (H : ℕ) : rationalIntervalVariableCount 0 0 H = 0 := by
  simp [rationalIntervalVariableCount]

theorem rational_interval_empty_physical_rows (H : ℕ) : rationalIntervalRowCount 0 0 H = 2+H := by
  simp [rationalIntervalRowCount]

theorem rational_empty_repertoire_keeps_interval_row_count (k m H : ℕ) :
    Fintype.card (RationalIntervalRows k m H ⊕ Fin 0) = rationalIntervalRowCount k m H := by
  rw [Fintype.card_sum, rational_interval_rows_exact_count, Fintype.card_fin, Nat.add_zero]

end SparseCompletion
