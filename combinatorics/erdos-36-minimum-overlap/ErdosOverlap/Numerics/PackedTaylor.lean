/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.PackedDot
public import ErdosOverlap.Numerics.TaylorGridCheck

/-!
# Whole Taylor rows from two exact packed dot products

All twenty scalar coefficient checks are recovered from the even and odd
packed sums. The parity, indexing, factor lengths and stored mass identities
are handled in the generic proof, rather than repeated in every data leaf.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def evenFactorRows (factors : ℕ → List ℤ) : List (List ℤ) :=
  (List.range 10).map (fun k => factors (2 * k))

@[expose] def oddFactorRows (factors : ℕ → List ℤ) : List (List ℤ) :=
  (List.range 10).map (fun k => factors (2 * k + 1))

@[expose] def storedScalarDot (even odd : List ℤ) (k : ℕ) : ℤ :=
  if k % 2 = 0 then even.getD (k / 2) 0 else odd.getD (k / 2) 0

@[expose] def storedScalarListCheck (masses : ℕ → ℤ) (even odd : List ℤ)
    (width j : ℕ) : ℕ → List ℤ → Bool
  | _, [] => true
  | k, p :: ps =>
      storedCoefficientCheck (storedScalarDot even odd k) (masses k) width j p &&
        storedScalarListCheck masses even odd width j (k + 1) ps

@[expose] def packedTaylorRowCheck (packedEven packedOdd : List ℤ)
    (masses : ℕ → ℤ) (width : ℕ) (row : List (ℤ × ℤ)) (j : ℕ)
    (dotsEven dotsOdd coefficients : List ℤ) : Bool :=
  packedSumCheck packedEven (row.map Prod.fst) dotsEven width 10 &&
    packedSumCheck packedOdd (row.map Prod.snd) dotsOdd width 10 &&
    decide (coefficients.length = 20) &&
    storedScalarListCheck masses dotsEven dotsOdd width j 0 coefficients

theorem evenFactorRows_length (factors : ℕ → List ℤ) : (evenFactorRows factors).length = 10 := by
  simp only [evenFactorRows, List.length_map, List.length_range]

theorem oddFactorRows_length (factors : ℕ → List ℤ) : (oddFactorRows factors).length = 10 := by
  simp only [oddFactorRows, List.length_map, List.length_range]

theorem evenFactorRows_getD (factors : ℕ → List ℤ) (k : ℕ) (hk : k < 10) :
    (evenFactorRows factors).getD k [] = factors (2 * k) := by
  simp [evenFactorRows, hk]

theorem oddFactorRows_getD (factors : ℕ → List ℤ) (k : ℕ) (hk : k < 10) :
    (oddFactorRows factors).getD k [] = factors (2 * k + 1) := by
  simp [oddFactorRows, hk]

theorem packedSumCheck_lengths {packed coordinates dots : List ℤ} {width count : ℕ}
    (h : packedSumCheck packed coordinates dots width count = true) :
    coordinates.length = width ∧ dots.length = count := by
  simp only [packedSumCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2.1⟩

theorem storedScalarListCheck_sound {masses : ℕ → ℤ} {even odd : List ℤ}
    {width j start : ℕ} {ps : List ℤ}
    (h : storedScalarListCheck masses even odd width j start ps = true)
    {k : ℕ} (hk : k < ps.length) :
    storedCoefficientCheck (storedScalarDot even odd (start + k))
      (masses (start + k)) width j (ps.getD k 0) = true := by
  induction ps generalizing start k with
  | nil => simp at hk
  | cons p ps ih =>
    simp only [storedScalarListCheck, Bool.and_eq_true] at h
    cases k with
    | zero => simpa only [Nat.add_zero, List.getD_cons_zero] using h.1
    | succ k =>
      have ht := ih h.2 (k := k) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)
      simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem coefficientListCheck_of_forall {factors : ℕ → List ℤ}
    {row : List (ℤ × ℤ)} {j start : ℕ} {ps : List ℤ}
    (h : ∀ k < ps.length,
      coefficientCheck (factors (start + k)) row j (start + k) (ps.getD k 0) = true) :
    coefficientListCheck factors row j start ps = true := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    have hh := h 0 (by simp only [List.length_cons]; omega)
    simp only [Nat.add_zero, List.getD_cons_zero] at hh
    simp only [coefficientListCheck, Bool.and_eq_true]
    refine ⟨hh, ih ?_⟩
    intro k hk
    have ht := h (k + 1) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)
    simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem completeCoefficientRowCheck_of_forall {factors : ℕ → List ℤ}
    {row : List (ℤ × ℤ)} {j : ℕ} {ps : List ℤ}
    (hlen : ps.length = 20)
    (h : ∀ k < ps.length, coefficientCheck (factors k) row j k (ps.getD k 0) = true) :
    completeCoefficientRowCheck factors row j ps = true := by
  simp only [completeCoefficientRowCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hlen, coefficientListCheck_of_forall ?_⟩
  simpa only [Nat.zero_add] using h

/-- Core wrapper with separately supplied, already checked packed sums. -/
theorem completeCoefficientRowCheck_of_packed
    {factors : ℕ → List ℤ} {masses : ℕ → ℤ} {width j : ℕ}
    {packedEven packedOdd dotsEven dotsOdd coefficients : List ℤ} {row : List (ℤ × ℤ)}
    (hpackEven : factorPackingCheck width (evenFactorRows factors) packedEven = true)
    (hpackOdd : factorPackingCheck width (oddFactorRows factors) packedOdd = true)
    (hmasses : ∀ k < 20, masses k = taylorFactorMass (factors k))
    (hEven : packedSumCheck packedEven (row.map Prod.fst) dotsEven width 10 = true)
    (hOdd : packedSumCheck packedOdd (row.map Prod.snd) dotsOdd width 10 = true)
    (hlen : coefficients.length = 20)
    (hscalar : storedScalarListCheck masses dotsEven dotsOdd width j 0 coefficients = true) :
    completeCoefficientRowCheck factors row j coefficients = true := by
  have hrowlen : row.length = width := by
    simpa only [List.length_map] using (packedSumCheck_lengths hEven).1
  have hEven' : packedSumCheck packedEven (row.map Prod.fst) dotsEven width
      (evenFactorRows factors).length = true := by
    simpa only [evenFactorRows_length] using hEven
  have hOdd' : packedSumCheck packedOdd (row.map Prod.snd) dotsOdd width
      (oddFactorRows factors).length = true := by
    simpa only [oddFactorRows_length] using hOdd
  apply completeCoefficientRowCheck_of_forall hlen
  intro k hk
  have hk20 : k < 20 := by omega
  have hk10 : k / 2 < 10 := by omega
  have hs := storedScalarListCheck_sound hscalar hk
  simp only [Nat.zero_add] at hs
  by_cases hpar : k % 2 = 0
  · have heven : 2 * (k / 2) = k := by omega
    have hd := packedSumCheck_getD_sound hpackEven hEven' (k / 2)
    rw [evenFactorRows_getD factors (k / 2) hk10,
      integerDot_cos_eq_taylorDot, heven] at hd
    have hdot : storedScalarDot dotsEven dotsOdd k = taylorDot (factors k) row k := by
      simpa only [storedScalarDot, ite_eq_left hpar] using hd
    have hmem : factors k ∈ evenFactorRows factors := by
      rw [← heven]
      exact List.mem_map.mpr ⟨k / 2, List.mem_range.mpr hk10, rfl⟩
    have hfactorlen := ((factorPackingCheck_sound hpackEven).2 _ hmem).1
    exact coefficientCheck_of_stored hdot (hmasses k hk20) hfactorlen.symm
      (hfactorlen.trans hrowlen.symm) hs
  · have hodd : 2 * (k / 2) + 1 = k := by omega
    have hd := packedSumCheck_getD_sound hpackOdd hOdd' (k / 2)
    rw [oddFactorRows_getD factors (k / 2) hk10,
      integerDot_sin_eq_taylorDot, hodd] at hd
    have hdot : storedScalarDot dotsEven dotsOdd k = taylorDot (factors k) row k := by
      simpa only [storedScalarDot, ite_eq_right hpar] using hd
    have hmem : factors k ∈ oddFactorRows factors := by
      rw [← hodd]
      exact List.mem_map.mpr ⟨k / 2, List.mem_range.mpr hk10, rfl⟩
    have hfactorlen := ((factorPackingCheck_sound hpackOdd).2 _ hmem).1
    exact coefficientCheck_of_stored hdot (hmasses k hk20) hfactorlen.symm
      (hfactorlen.trans hrowlen.symm) hs

theorem packedTaylorRowCheck_sound
    {factors : ℕ → List ℤ} {masses : ℕ → ℤ} {width j : ℕ}
    {packedEven packedOdd dotsEven dotsOdd coefficients : List ℤ} {row : List (ℤ × ℤ)}
    (hpackEven : factorPackingCheck width (evenFactorRows factors) packedEven = true)
    (hpackOdd : factorPackingCheck width (oddFactorRows factors) packedOdd = true)
    (hmasses : ∀ k < 20, masses k = taylorFactorMass (factors k))
    (h : packedTaylorRowCheck packedEven packedOdd masses width row j
      dotsEven dotsOdd coefficients = true) :
    completeCoefficientRowCheck factors row j coefficients = true := by
  simp only [packedTaylorRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact completeCoefficientRowCheck_of_packed hpackEven hpackOdd hmasses
    h.1.1.1 h.1.1.2 h.1.2 h.2

end
end ErdosOverlap.Numerics
