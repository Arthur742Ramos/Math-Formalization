module

public import ErdosOverlap.Numerics.Rotation
public import ErdosOverlap.Numerics.CachedTrig

/-! # Finite certificates for trigonometric values on the uniform Taylor grid -/

namespace ErdosOverlap.Numerics

open LeanCert.Core

@[expose] public section

def rotationScalarError : ℤ := 34028236692093846346338
def rotationSeedError : ℤ := 2*rotationScalarError

theorem rotationScalarError_nonneg : 0 ≤ rotationScalarError := by norm_num [rotationScalarError]

noncomputable def rotationAngle (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

theorem rotationAngle_norm (θ : ℝ) : ‖rotationAngle θ‖ = 1 := by
  have hs : ‖rotationAngle θ‖^2 = 1 := by
    rw [Complex.sq_norm]
    simp only [rotationAngle, Complex.normSq_apply]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (rotationAngle θ)]

theorem rotationAngle_add (θ φ : ℝ) : rotationAngle (θ+φ) = rotationAngle θ*rotationAngle φ := by
  apply Complex.ext <;> simp [rotationAngle, Real.cos_add, Real.sin_add]
  ring

theorem rotationAngle_pow (θ : ℝ) (j : ℕ) : (rotationAngle θ)^j = rotationAngle ((j : ℝ)*θ) := by
  induction j with
  | zero => apply Complex.ext <;> simp [rotationAngle]
  | succ j ih =>
    rw [pow_succ, ih, ← rotationAngle_add]
    congr 1
    push_cast
    ring

def FixedBox.nearCheck (I : FixedBox) (u E : ℤ) : Bool :=
  decide (u-E ≤ I.lo ∧ I.hi ≤ u+E)

theorem FixedBox.nearCheck_sound {x : ℝ} {I : FixedBox} {u E : ℤ}
    (hx : x ∈ I) (h : I.nearCheck u E = true) :
    |(u : ℝ)/fixedScale-x| ≤ (E : ℝ)/fixedScale := by
  simp only [FixedBox.nearCheck, decide_eq_true_eq] at h
  have hl : (u : ℝ)-(E : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast h.1
  have hh : (I.hi : ℝ) ≤ (u : ℝ)+(E : ℝ) := by exact_mod_cast h.2
  have hb : |(u : ℝ)-x*fixedScale| ≤ (E : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hd := div_le_div_of_nonneg_right hb fixedScale_real_pos.le
  have hne := ne_of_gt fixedScale_real_pos
  have he : (u : ℝ)/fixedScale-x = ((u : ℝ)-x*fixedScale)/fixedScale := by
    field_simp
  rw [he, abs_div, abs_of_pos fixedScale_real_pos]
  exact hd

structure RotationSeed where
  initial : ℤ × ℤ
  step : ℤ × ℤ
  deriving DecidableEq, Repr

def RotationSeed.check (seed : RotationSeed) (frequency : ℚ) : Bool :=
  let initialArg := FixedBox.ofRat (frequency/1024)
  let stepArg := FixedBox.ofRat (2*frequency/1024)
  decide (seed.step.1^2+seed.step.2^2 ≤ fixedScale^2) &&
    initialArg.cos32.nearCheck seed.initial.1 rotationScalarError &&
    initialArg.sin32.nearCheck seed.initial.2 rotationScalarError &&
    stepArg.cos32.nearCheck seed.step.1 rotationScalarError &&
    stepArg.sin32.nearCheck seed.step.2 rotationScalarError

theorem RotationSeed.check_sound {seed : RotationSeed} {frequency : ℚ}
    (h : seed.check frequency = true) :
    seed.step.1^2+seed.step.2^2 ≤ fixedScale^2 ∧
    ‖rotationValue seed.initial-rotationAngle ((frequency/1024 : ℚ) : ℝ)‖ ≤
      (rotationSeedError : ℝ)/fixedScale ∧
    ‖rotationFactor seed.step.1 seed.step.2-rotationAngle ((2*frequency/1024 : ℚ) : ℝ)‖ ≤
      (rotationSeedError : ℝ)/fixedScale := by
  simp only [RotationSeed.check, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hcs, hic⟩, his⟩, hsc⟩, hss⟩
  have hir := FixedBox.nearCheck_sound (FixedBox.mem_cos32 (FixedBox.mem_ofRat (frequency/1024))) hic
  have hii := FixedBox.nearCheck_sound (FixedBox.mem_sin32 (FixedBox.mem_ofRat (frequency/1024))) his
  have hsr := FixedBox.nearCheck_sound (FixedBox.mem_cos32 (FixedBox.mem_ofRat (2*frequency/1024))) hsc
  have hsi := FixedBox.nearCheck_sound (FixedBox.mem_sin32 (FixedBox.mem_ofRat (2*frequency/1024))) hss
  refine ⟨hcs, ?_, ?_⟩
  · have ht := complex_norm_sub_le_of_coordinate_bounds (u := rotationValue seed.initial)
      (z := rotationAngle ((frequency/1024 : ℚ) : ℝ)) hir hii
    convert! ht using 1
    simp only [rotationSeedError, Int.cast_mul, Int.cast_ofNat]
    ring
  · have ht := complex_norm_sub_le_of_coordinate_bounds (u := rotationFactor seed.step.1 seed.step.2)
      (z := rotationAngle ((2*frequency/1024 : ℚ) : ℝ)) hsr hsi
    convert! ht using 1
    simp only [rotationSeedError, Int.cast_mul, Int.cast_ofNat]
    ring

structure RotationBank where
  seed : RotationSeed
  states : Array (ℤ × ℤ)
  deriving DecidableEq, Repr

def RotationBank.state (bank : RotationBank) (j : ℕ) : ℤ × ℤ := bank.states[j]?.getD (0,0)

def RotationBank.chainCheck (bank : RotationBank) : Bool :=
  decide (bank.states.size=1024) && decide (bank.state 0=bank.seed.initial) &&
    (List.range 1023).all (fun j => decide
      (bank.state (j+1)=rotationStep bank.seed.step.1 bank.seed.step.2 (bank.state j)))

def RotationBank.check (bank : RotationBank) (frequency : ℚ) : Bool :=
  bank.seed.check frequency && bank.chainCheck

theorem RotationBank.state_eq_iter {bank : RotationBank} (h : bank.chainCheck = true)
    {j : ℕ} (hj : j < 1024) :
    bank.state j = rotationIter bank.seed.step.1 bank.seed.step.2 bank.seed.initial j := by
  simp only [RotationBank.chainCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases h with ⟨⟨_, hzero⟩, hstep⟩
  induction j with
  | zero => exact hzero
  | succ j ih =>
    have hrec := hstep j (List.mem_range.mpr (by omega))
    rw [hrec, ih (by omega)]
    rfl

theorem RotationBank.trig_mem {bank : RotationBank} {frequency : ℚ}
    (h : bank.check frequency = true) {j : ℕ} (hj : j < 1024) :
    Real.cos ((frequency*((2*j+1 : ℕ) : ℚ)/1024 : ℚ) : ℝ) ∈
      rotationCoordinateBox (bank.state j).1 (rotationRadius rotationSeedError rotationSeedError j) ∧
    Real.sin ((frequency*((2*j+1 : ℕ) : ℚ)/1024 : ℚ) : ℝ) ∈
      rotationCoordinateBox (bank.state j).2 (rotationRadius rotationSeedError rotationSeedError j) := by
  simp only [RotationBank.check, Bool.and_eq_true] at h
  obtain ⟨hcs, hi, hs⟩ := RotationSeed.check_sound h.1
  have hb := rotationIter_mem_boxes bank.seed.initial hcs
    (rotationAngle_norm ((2*frequency/1024 : ℚ) : ℝ))
    (rotationAngle_norm ((frequency/1024 : ℚ) : ℝ)) hi hs j
  rw [← bank.state_eq_iter h.2 hj] at hb
  rw [rotationAngle_pow, ← rotationAngle_add] at hb
  have he : (j : ℝ)*((2*frequency/1024 : ℚ) : ℝ)+((frequency/1024 : ℚ) : ℝ) =
      ((frequency*((2*j+1 : ℕ) : ℚ)/1024 : ℚ) : ℝ) := by
    push_cast
    ring
  rw [he] at hb
  exact hb

end
end ErdosOverlap.Numerics
