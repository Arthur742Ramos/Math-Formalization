/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Exact batching of integer dot-product certificates

Several dot products are packed as balanced digits in one large integer.
Bilinearity gives the packed value. A proved digit-size bound makes this
encoding injective, so equality of packed integers recovers every exact dot
product. This is deterministic integer arithmetic, not a hash check.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def integerPack (base : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: rest => a + base * integerPack base rest

@[expose] def integerDot : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + integerDot as bs
  | _, _ => 0

theorem integerDot_nil_right (xs : List ℤ) : integerDot xs [] = 0 := by
  cases xs <;> rfl

@[expose] def packFactorRows (base : ℤ) (width : ℕ) : List (List ℤ) → List ℤ
  | [] => List.replicate width 0
  | factors :: rest => List.zipWith (fun a b => a + base * b)
      factors (packFactorRows base width rest)

@[expose] def packedBase : ℤ := 2 ^ 272

@[expose] def packedCoordinateBound : ℤ := 2 * fixedScale

@[expose] def packedDotBound : ℤ := 2 * fixedScale ^ 2

@[expose] def factorPackingCheck (width : ℕ) (rows : List (List ℤ))
    (packed : List ℤ) : Bool :=
  decide (packed = packFactorRows packedBase width rows) &&
    rows.all (fun fs => decide (fs.length = width ∧ taylorFactorMass fs ≤ fixedScale))

@[expose] def packedSumCheck (packed coordinates dots : List ℤ)
    (width digitCount : ℕ) : Bool :=
  decide (coordinates.length = width ∧ dots.length = digitCount ∧
    integerDot packed coordinates = integerPack packedBase dots) &&
    coordinates.all (fun x => decide (|x| ≤ packedCoordinateBound)) &&
    dots.all (fun x => decide (|x| ≤ packedDotBound))

@[expose] def storedCoefficientCheck (dot mass : ℤ) (width j : ℕ) (p : ℤ) : Bool :=
  decide (|dot - p * (fixedScale ^ 2 / quantizedCoefficientScale)| +
    mass * rotationRadius rotationSeedError rotationSeedError j +
    (width : ℤ) * fixedScale ≤ fixedScale ^ 2 / quantizedCoefficientToleranceDenominator)

theorem integerPack_injective_bounded {base bound : ℤ} (hbase : 0 < base)
    (hgap : 2 * bound < base) {xs ys : List ℤ}
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, |x| ≤ bound) (hy : ∀ y ∈ ys, |y| ≤ bound)
    (heq : integerPack base xs = integerPack base ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    have hnil : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    exact hnil.symm
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have ha := hx a List.mem_cons_self
      have hb := hy b List.mem_cons_self
      have hdifference : |a - b| < base := by
        have htriangle := abs_sub_le a 0 b
        simp only [sub_zero, zero_sub, abs_neg] at htriangle
        omega
      have hdvd : base ∣ a - b := by
        refine ⟨integerPack base ys - integerPack base xs, ?_⟩
        simp only [integerPack] at heq
        nlinarith
      have hab : a = b := sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd hdifference)
      subst b
      have htail : integerPack base xs = integerPack base ys := by
        simp only [integerPack] at heq
        exact mul_left_cancel₀ (ne_of_gt hbase) (add_left_cancel heq)
      congr 1
      exact ih (Nat.succ.inj hlen)
        (fun x hx' => hx x (List.mem_cons_of_mem a hx'))
        (fun y hy' => hy y (List.mem_cons_of_mem a hy')) htail

theorem taylorFactorMass_nonneg (xs : List ℤ) : 0 ≤ taylorFactorMass xs := by
  induction xs with
  | nil => simp only [taylorFactorMass, le_refl]
  | cons x xs ih => exact add_nonneg (abs_nonneg _) ih

theorem integerDot_abs_le {xs ys : List ℤ} {bound : ℤ}
    (hbound : 0 ≤ bound) (hy : ∀ y ∈ ys, |y| ≤ bound) :
    |integerDot xs ys| ≤ taylorFactorMass xs * bound := by
  induction xs generalizing ys with
  | nil => simp only [integerDot, taylorFactorMass, abs_zero, zero_mul, le_refl]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [integerDot, abs_zero]
      exact mul_nonneg (taylorFactorMass_nonneg _) hbound
    | cons y ys =>
      have ht := ih (fun z hz => hy z (List.mem_cons_of_mem y hz))
      have hh : |x * y| ≤ |x| * bound := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hy y List.mem_cons_self) (abs_nonneg _)
      simp only [integerDot, taylorFactorMass]
      exact ((abs_add_le _ _).trans (add_le_add hh ht)).trans_eq (by ring)

theorem integerDot_replicate_zero (width : ℕ) (ys : List ℤ) :
    integerDot (List.replicate width 0) ys = 0 := by
  induction width generalizing ys with
  | zero => simp only [List.replicate_zero, integerDot]
  | succ width ih =>
    cases ys with
    | nil => exact integerDot_nil_right _
    | cons y ys => simp only [List.replicate_succ, integerDot, zero_mul, zero_add, ih]

theorem integerDot_zipWith_add_scale (base : ℤ) {xs ys : List ℤ}
    (hlen : xs.length = ys.length) (coordinates : List ℤ) :
    integerDot (List.zipWith (fun x y => x + base * y) xs ys) coordinates =
      integerDot xs coordinates + base * integerDot ys coordinates := by
  induction xs generalizing ys coordinates with
  | nil =>
    have hnil : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp only [List.zipWith_nil_left, integerDot, mul_zero, add_zero]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      cases coordinates with
      | nil => simp only [integerDot_nil_right, mul_zero, add_zero]
      | cons c cs =>
        simp only [List.zipWith_cons_cons, integerDot]
        rw [ih (Nat.succ.inj hlen)]
        ring

theorem packFactorRows_length (base : ℤ) (width : ℕ) {rows : List (List ℤ)}
    (hlen : ∀ fs ∈ rows, fs.length = width) :
    (packFactorRows base width rows).length = width := by
  induction rows with
  | nil => simp only [packFactorRows, List.length_replicate]
  | cons fs rows ih =>
    have hfs := hlen fs List.mem_cons_self
    have ht := ih (fun gs hgs => hlen gs (List.mem_cons_of_mem fs hgs))
    simp only [packFactorRows, List.length_zipWith, hfs, ht, min_self]

theorem integerDot_packFactorRows (base : ℤ) (width : ℕ)
    {rows : List (List ℤ)} (coordinates : List ℤ)
    (hlen : ∀ fs ∈ rows, fs.length = width) :
    integerDot (packFactorRows base width rows) coordinates =
      integerPack base (rows.map (fun fs => integerDot fs coordinates)) := by
  induction rows with
  | nil => simp only [packFactorRows, integerDot_replicate_zero, List.map_nil, integerPack]
  | cons fs rows ih =>
    have hfs := hlen fs List.mem_cons_self
    have htail : ∀ gs ∈ rows, gs.length = width :=
      fun gs hgs => hlen gs (List.mem_cons_of_mem fs hgs)
    simp only [packFactorRows, List.map_cons, integerPack]
    rw [integerDot_zipWith_add_scale base (hfs.trans (packFactorRows_length base width htail).symm),
      ih htail]

theorem packedBase_pos : 0 < packedBase := by
  exact pow_pos (by norm_num : (0 : ℤ) < 2) _

theorem packedCoordinateBound_nonneg : 0 ≤ packedCoordinateBound := by
  exact mul_nonneg (by norm_num) fixedScale_pos.le

set_option exponentiation.threshold 300 in
theorem packedBase_gap : 2 * packedDotBound < packedBase := by
  norm_num [packedBase, packedDotBound, fixedScale]

theorem factorPackingCheck_sound {width : ℕ} {rows : List (List ℤ)} {packed : List ℤ}
    (h : factorPackingCheck width rows packed = true) :
    packed = packFactorRows packedBase width rows ∧
      ∀ fs ∈ rows, fs.length = width ∧ taylorFactorMass fs ≤ fixedScale := by
  simpa only [factorPackingCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem packedSumCheck_sound {width : ℕ} {rows : List (List ℤ)}
    {packed coordinates dots : List ℤ}
    (hf : factorPackingCheck width rows packed = true)
    (hd : packedSumCheck packed coordinates dots width rows.length = true) :
    dots = rows.map (fun fs => integerDot fs coordinates) := by
  obtain ⟨hpacked, hrows⟩ := factorPackingCheck_sound hf
  simp only [packedSumCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hd
  have heq : integerPack packedBase dots =
      integerPack packedBase (rows.map (fun fs => integerDot fs coordinates)) := by
    rw [← hd.1.1.2.2, hpacked]
    exact integerDot_packFactorRows packedBase width coordinates (fun fs hfs => (hrows fs hfs).1)
  apply integerPack_injective_bounded packedBase_pos packedBase_gap
    (hd.1.1.2.1.trans (List.length_map _).symm) hd.2 _ heq
  intro d hdmem
  obtain ⟨fs, hfs, rfl⟩ := List.mem_map.mp hdmem
  have hdot := integerDot_abs_le (xs := fs) packedCoordinateBound_nonneg hd.1.2
  have hmass := mul_le_mul_of_nonneg_right (hrows fs hfs).2 packedCoordinateBound_nonneg
  exact hdot.trans (hmass.trans_eq (by unfold packedCoordinateBound packedDotBound; ring))

theorem integerDot_getD_map (rows : List (List ℤ)) (coordinates : List ℤ) (k : ℕ) :
    (rows.map (fun fs => integerDot fs coordinates)).getD k 0 =
      integerDot (rows.getD k []) coordinates := by
  induction rows generalizing k with
  | nil => simp [integerDot]
  | cons fs rows ih =>
    cases k with
    | zero => simp only [List.map_cons, List.getD_cons_zero]
    | succ k => simpa only [List.map_cons, List.getD_cons_succ] using ih k

theorem packedSumCheck_getD_sound {width : ℕ} {rows : List (List ℤ)}
    {packed coordinates dots : List ℤ}
    (hf : factorPackingCheck width rows packed = true)
    (hd : packedSumCheck packed coordinates dots width rows.length = true) (k : ℕ) :
    dots.getD k 0 = integerDot (rows.getD k []) coordinates := by
  rw [packedSumCheck_sound hf hd]
  exact integerDot_getD_map rows coordinates k

theorem taylorDot_eq_integerDot (factors : List ℤ) (row : List (ℤ × ℤ)) (k : ℕ) :
    taylorDot factors row k =
      integerDot factors (row.map (fun state => taylorCoordinate state k)) := by
  induction factors generalizing row with
  | nil => cases row <;> rfl
  | cons f fs ih =>
    cases row with
    | nil => rfl
    | cons state row => simp only [taylorDot, List.map_cons, integerDot, ih]

theorem integerDot_cos_eq_taylorDot (factors : List ℤ) (row : List (ℤ × ℤ)) (k : ℕ) :
    integerDot factors (row.map Prod.fst) = taylorDot factors row (2 * k) := by
  rw [taylorDot_eq_integerDot]
  congr 1
  apply List.map_congr_left
  intro state _
  simp only [taylorCoordinate, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, ite_true]

theorem integerDot_sin_eq_taylorDot (factors : List ℤ) (row : List (ℤ × ℤ)) (k : ℕ) :
    integerDot factors (row.map Prod.snd) = taylorDot factors row (2 * k + 1) := by
  rw [taylorDot_eq_integerDot]
  congr 1
  apply List.map_congr_left
  intro state _
  simp only [taylorCoordinate, Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul,
    Nat.zero_mod, zero_add, Nat.mod_eq_of_lt (by norm_num : 1 < 2),
    Nat.one_ne_zero, ite_false]

/-- Recover an existing coefficient check without re-evaluating its dot
product, once exact packing has proved that the stored dot is the true one. -/
theorem coefficientCheck_of_stored {factors : List ℤ} {row : List (ℤ × ℤ)}
    {j k width : ℕ} {p dot mass : ℤ}
    (hdot : dot = taylorDot factors row k)
    (hmass : mass = taylorFactorMass factors) (hwidth : width = factors.length)
    (hlen : factors.length = row.length)
    (hc : storedCoefficientCheck dot mass width j p = true) :
    coefficientCheck factors row j k p = true := by
  simp only [storedCoefficientCheck, decide_eq_true_eq] at hc
  simp only [coefficientCheck, decide_eq_true_eq]
  exact ⟨hlen, by simpa only [hdot, hmass, hwidth] using hc⟩

end
end ErdosOverlap.Numerics
