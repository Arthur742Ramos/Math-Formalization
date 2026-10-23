/- AI-assisted original-input and transient-value continuation; Apache-2.0.
Exact compilation/audit status is recorded in source-bound receipts.
The uncompiled original draft remains in source-input-bits-v1.
These are value/encoding bounds, not primitive or total running-time claims.
-/
module
public import ProtectedSources.GaussianOutputBits
@[expose] public section
namespace SparseCompletion.Gaussian

/-- Scaling transports the real operational trace, preserving its actual pivot
rows and original column labels. It does not replace the runtime algorithm. -/
theorem minorStage_scale {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) (c : ℚ) (hc : c ≠ 0) :
    MinorStage (scaleTable c A) k n P Q σ (scaleTable c B) := by
  induction h with
  | initial => exact MinorStage.initial
  | @step k n P Q σ B previous p hp ih =>
    have hps : firstNonzero r (fun i => entry (scaleTable c B) i 0) = some p := by
      rw [entry_scaleTable, firstNonzero_scale r c hc, hp]
    have hs := MinorStage.step ih p hps
    rw [residual_scaleTable B p c hc] at hs
    exact hs

/-- Entry heights of the ORIGINAL rational execution. The scaling factor D is
put back into the denominator, so this does not silently price the integer-
scaled equivalent algorithm in place of the actual rational run. -/
theorem minorStage_original_rational_height {r N k n : ℕ}
    (A : QTable r N) (H : ℕ)
    (hH : ∀ i j, (Matrix.num (entry A) i j).natAbs ≤ H)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (hs : MinorStage A k n P Q σ B) :
    ∀ i j, (entry B i j).num.natAbs ≤ (k+1).factorial * H^(k+1) ∧
      (entry B i j).den ≤ Matrix.den (entry A) * (k.factorial * H^k) := by
  classical
  let Z : Matrix (Fin r) (Fin N) ℤ := Matrix.num (entry A)
  let D : ℕ := Matrix.den (entry A)
  have hD : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Matrix.den_ne_zero (entry A))
  have hsc := minorStage_scale hs (D : ℚ) hD
  rw [← integerNumeratorTable_eq_scale] at hsc
  have hint := minorStage_invariant hsc
  intro i j
  let V : Matrix (PrefixIndex k) (PrefixIndex k) ℤ := Matrix.submatrix Z P Q
  let U : Matrix (PrefixIndex k ⊕ Unit) (PrefixIndex k ⊕ Unit) ℤ :=
    Matrix.submatrix Z (appendMap P i) (appendMap Q (σ j))
  have hdV : (selectedBlock (entry (integerNumeratorTable A)) P Q).det = (V.det : ℚ) := by
    change (selectedBlock (entry (tableOfFn (fun a b => (Z a b : ℚ)))) P Q).det = _
    rw [entry_tableOfFn_function]
    exact intCast_det V
  have hdU : (selectedBorder (entry (integerNumeratorTable A)) P Q i (σ j)).det =
      (U.det : ℚ) := by
    change (selectedBorder (entry (tableOfFn (fun a b => (Z a b : ℚ)))) P Q i (σ j)).det = _
    rw [entry_tableOfFn_function]
    exact intCast_det U
  have hvq : (V.det : ℚ) ≠ 0 := by simpa only [hdV] using hint.1
  have hv : V.det ≠ 0 := Int.cast_ne_zero.mp hvq
  have hec : (D : ℚ) * entry B i j = (U.det : ℚ) / (V.det : ℚ) := by
    simpa only [entry_scaleTable, hdU, hdV] using hint.2 i j
  have hden : (D : ℤ) * V.det ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr (Matrix.den_ne_zero (entry A))) hv
  have he : entry B i j = (U.det : ℚ) / (((D : ℤ) * V.det : ℤ) : ℚ) := by
    calc
      entry B i j = ((D : ℚ) * entry B i j) / (D : ℚ) := by field_simp [hD]
      _ = ((U.det : ℚ) / (V.det : ℚ)) / (D : ℚ) := by rw [hec]
      _ = (U.det : ℚ) / (((D : ℤ) * V.det : ℤ) : ℚ) := by push_cast; ring
  have hUb : U.det.natAbs ≤ (k+1).factorial * H^(k+1) := by
    let e := (Fintype.equivFin (PrefixIndex k ⊕ Unit)).symm
    have hd := determinant_height (U.submatrix e e) H
      (fun a b => hH (appendMap P i (e a)) (appendMap Q (σ j) (e b)))
    simpa only [Matrix.det_submatrix_equiv_self, Fintype.card_sum,
      Fintype.card_unit, prefixIndex_card] using hd
  have hVb : V.det.natAbs ≤ k.factorial * H^k := by
    let e := (Fintype.equivFin (PrefixIndex k)).symm
    have hd := determinant_height (V.submatrix e e) H (fun a b => hH (P (e a)) (Q (e b)))
    simpa only [Matrix.det_submatrix_equiv_self, prefixIndex_card] using hd
  rw [he]
  constructor
  · exact (quotient_num_height U.det ((D : ℤ) * V.det) hden).trans hUb
  · apply (quotient_den_height U.det ((D : ℤ) * V.det) hden).trans
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul_left D hVb

/-- Original-input bounds for actual rational residual entries. This is a
mathematical value invariant of every real stage, not a runtime-cost premise. -/
theorem minorStage_height_from_original_input {r N k n : ℕ}
    (A : QTable r N) (Bbits : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^Bbits)
    (hden : ∀ i j, (entry A i j).den ≤ 2^Bbits)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {C : QTable r n}
    (hs : MinorStage A k n P Q σ C) :
    ∀ i j, (entry C i j).num.natAbs ≤
        (k+1).factorial * (2^(clearedInputExponent r N Bbits))^(k+1) ∧
      (entry C i j).den ≤
        (2^Bbits)^(r*N) * (k.factorial * (2^(clearedInputExponent r N Bbits))^k) := by
  intro i j
  have hh := minorStage_original_rational_height A (2^(clearedInputExponent r N Bbits))
    (matrix_num_bound_from_input_bits (entry A) Bbits hnum hden) hs i j
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply Nat.mul_le_mul_right
  exact (matrix_den_le_input_product (entry A)).trans
    (inputDenominatorProduct_le (entry A) (2^Bbits) hden)

/-- Generic quotient arithmetic: both reduced encoding components are bounded
by cross-products of actual operand numerator/denominator bounds. -/
theorem rational_div_height (q s : ℚ) (hqN hqD hsN hsD : ℕ)
    (hqnum : q.num.natAbs ≤ hqN) (hqden : q.den ≤ hqD)
    (hsnum : s.num.natAbs ≤ hsN) (hsden : s.den ≤ hsD) (hs : s ≠ 0) :
    (q/s).num.natAbs ≤ hqN*hsD ∧ (q/s).den ≤ hqD*hsN := by
  have hsn : s.num ≠ 0 := by intro hn; exact hs (Rat.zero_of_num_zero hn)
  have hd : (q.den : ℤ) * s.num ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) hsn
  have he : q/s = ((q.num * (s.den : ℤ) : ℤ) : ℚ) /
      (((q.den : ℤ) * s.num : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den s]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he]
  constructor
  · apply (quotient_num_height _ _ hd).trans
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hqnum hsden
  · apply (quotient_den_height _ _ hd).trans
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hqden hsnum

/-- The actual pivot division used by residual and lift now has an earned
original-input operand bound. No minor or pivot-height witness is supplied. -/
theorem minorStage_actual_pivot_division_height {r N k n : ℕ}
    (A : QTable r N) (Bbits : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^Bbits)
    (hden : ∀ i j, (entry A i j).den ≤ 2^Bbits)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin (n+1) → Fin N} {C : QTable r (n+1)}
    (hs : MinorStage A k (n+1) P Q σ C) (p : Fin r)
    (hp : firstNonzero r (fun i => entry C i 0) = some p) :
    ∀ j : Fin n, let M := (k+1).factorial * (2^(clearedInputExponent r N Bbits))^(k+1)
      let D := (2^Bbits)^(r*N) * (k.factorial * (2^(clearedInputExponent r N Bbits))^k)
      (entry C p j.succ / entry C p 0).num.natAbs ≤ M*D ∧
      (entry C p j.succ / entry C p 0).den ≤ D*M := by
  intro j
  have hentry := minorStage_height_from_original_input A Bbits hnum hden hs
  exact rational_div_height _ _ _ _ _ _ (hentry p j.succ).1 (hentry p j.succ).2
    (hentry p 0).1 (hentry p 0).2 (firstNonzero_some r _ p hp)

def stageNumeratorExponent (r N B k : ℕ) : ℕ :=
  (k+1)*(k+1) + clearedInputExponent r N B*(k+1)

def stageDenominatorExponent (r N B k : ℕ) : ℕ :=
  B*(r*N) + (k*k + clearedInputExponent r N B*k)

theorem stage_numerator_magnitude_le_two_pow (r N B k : ℕ) :
    (k+1).factorial * (2^(clearedInputExponent r N B))^(k+1) ≤
      2^(stageNumeratorExponent r N B k) := by
  exact (le_max_right 1 _).trans
    (factorial_times_pow_two_le (k+1) (clearedInputExponent r N B))

theorem stage_denominator_magnitude_le_two_pow (r N B k : ℕ) :
    (2^B)^(r*N) * (k.factorial * (2^(clearedInputExponent r N B))^k) ≤
      2^(stageDenominatorExponent r N B k) := by
  calc
    _ ≤ (2^B)^(r*N) * 2^(k*k+clearedInputExponent r N B*k) :=
      Nat.mul_le_mul_left _ ((le_max_right 1 _).trans
        (factorial_times_pow_two_le k (clearedInputExponent r N B)))
    _ = _ := by rw [← pow_mul, ← pow_add]; rfl

/-- Binary digit bounds for every normalized value stored in an ORIGINAL
rational residual table, from original input bits and actual reached stage. -/
theorem minorStage_entry_bits_from_original_input {r N k n : ℕ}
    (A : QTable r N) (Bbits : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^Bbits)
    (hden : ∀ i j, (entry A i j).den ≤ 2^Bbits)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {C : QTable r n}
    (hs : MinorStage A k n P Q σ C) :
    ∀ i j, Nat.size (entry C i j).num.natAbs ≤ stageNumeratorExponent r N Bbits k+1 ∧
      Nat.size (entry C i j).den ≤ stageDenominatorExponent r N Bbits k+1 := by
  intro i j
  have hh := minorStage_height_from_original_input A Bbits hnum hden hs i j
  exact ⟨nat_size_le_of_le_two_pow _ _ (hh.1.trans (stage_numerator_magnitude_le_two_pow r N Bbits k)),
    nat_size_le_of_le_two_pow _ _ (hh.2.trans (stage_denominator_magnitude_le_two_pow r N Bbits k))⟩

/-- Actual pivot division bit lengths, including divisions recomputed inside
each lift getter. Repetition changes event counts but not this value bound. -/
theorem minorStage_pivot_division_bits_from_original_input {r N k n : ℕ}
    (A : QTable r N) (Bbits : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^Bbits)
    (hden : ∀ i j, (entry A i j).den ≤ 2^Bbits)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin (n+1) → Fin N} {C : QTable r (n+1)}
    (hs : MinorStage A k (n+1) P Q σ C) (p : Fin r)
    (hp : firstNonzero r (fun i => entry C i 0) = some p) :
    ∀ j : Fin n,
      Nat.size (entry C p j.succ / entry C p 0).num.natAbs ≤
        stageNumeratorExponent r N Bbits k + stageDenominatorExponent r N Bbits k + 1 ∧
      Nat.size (entry C p j.succ / entry C p 0).den ≤
        stageNumeratorExponent r N Bbits k + stageDenominatorExponent r N Bbits k + 1 := by
  intro j
  have hpiv := minorStage_actual_pivot_division_height A Bbits hnum hden hs p hp j
  have hmul := Nat.mul_le_mul (stage_numerator_magnitude_le_two_pow r N Bbits k)
    (stage_denominator_magnitude_le_two_pow r N Bbits k)
  rw [← pow_add] at hmul
  constructor
  · exact nat_size_le_of_le_two_pow _ _ (hpiv.1.trans hmul)
  · apply nat_size_le_of_le_two_pow
    apply hpiv.2.trans
    simpa only [Nat.mul_comm] using hmul

end SparseCompletion.Gaussian
