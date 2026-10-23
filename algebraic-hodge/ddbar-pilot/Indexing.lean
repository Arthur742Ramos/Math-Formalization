module

public import Integration

/-!
# Conventional E1 indexing data

This is indexing infrastructure for the genuine spectral-object API. For a
future increasing filtration functor `i ↦ F^(-i)`, the central interval at
`(p,q)` is `F^(p+1) → F^p`. Thus its first-page cohomology is the candidate
for vertical cohomology. No filtration functor, associated spectral object,
`HasSpectralSequence` instance, or first-page comparison is constructed here.
In particular, these arithmetic proofs assert no degeneration result.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicHodgePilot

/-- Coordinates relating conventional filtration degrees to mathlib's
canonical E2 core; the corresponding canonical page number is `r+1`. -/
def canonicalCoordinates (pq : ℤ × ℤ) : ℤ × ℤ :=
  (2 * pq.1 + pq.2 + 1, -pq.1 - 1)

theorem canonicalCoordinates_totalDegree (pq : ℤ × ℤ) :
    (canonicalCoordinates pq).1 + (canonicalCoordinates pq).2 = pq.1 + pq.2 := by
  dsimp [canonicalCoordinates]
  lia -abstractProof

/-- The conventional `d_r` shift becomes the canonical `d_(r+1)` shift.
This proves the degree correspondence only, not a page comparison. -/
theorem canonicalCoordinates_differentialDegree (pq : ℤ × ℤ) (r : ℤ) :
    canonicalCoordinates (pq + (r, 1 - r)) =
      canonicalCoordinates pq + (r + 1, 1 - (r + 1)) := by
  ext <;> dsimp [canonicalCoordinates] <;> lia -abstractProof

/-- Data beginning at conventional E1, with differential degree `(r,1-r)`.
The interval formulas use increasing filtration indices `i ↦ F^(-i)`. -/
def e1Data : Abelian.SpectralObject.SpectralSequenceDataCore EInt
    (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq _ := (-pq.1 - r : ℤ)
  i₁ pq := (-pq.1 - 1 : ℤ)
  i₂ pq := (-pq.1 : ℤ)
  i₃ r pq _ := (-pq.1 + r - 1 : ℤ)
  le₀₁ r pq hr := by simp; lia -abstractProof
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia -abstractProof
  hc := by rintro r pq _ rfl _; dsimp; lia -abstractProof
  hc₀₂ := by rintro r pq _ rfl _; simp; lia -abstractProof
  hc₁₃ := by rintro r pq _ rfl _; simp
  antitone_i₀ r r' pq hr hrr' := by simp; lia -abstractProof
  monotone_i₃ r r' pq hr hrr' := by simp; lia -abstractProof
  i₀_prev := by rintro r r' pq _ rfl hrr' hr; dsimp; congr 1; lia -abstractProof
  i₃_next := by rintro r r' pq _ rfl hrr' hr; dsimp; congr 1; lia -abstractProof

/-- At page 1 the first outer interval is the identity interval. -/
theorem e1Data_first_left (pq : ℤ × ℤ) :
    e1Data.i₀ 1 pq = e1Data.i₁ pq :=
  rfl

/-- At page 1 the last outer interval is the identity interval. -/
theorem e1Data_first_right (pq : ℤ × ℤ) :
    e1Data.i₂ pq = e1Data.i₃ 1 pq := by
  dsimp [e1Data]
  congr 1
  lia -abstractProof

end AlgebraicHodgePilot
