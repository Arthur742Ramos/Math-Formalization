module

public import ErdosOverlap.Numerics.FixedTrig

/-! # Reusable integer Taylor coefficients

All coefficient enclosures are checked once. Subsequent transcendental
computations perform integer arithmetic on these cached enclosures.
-/

namespace ErdosOverlap.Numerics.FixedBox

open LeanCert.Core

@[expose] public section

def rationalCheck (I : FixedBox) (q : ℚ) : Bool :=
  decide ((I.lo : ℚ) ≤ q*fixedScale ∧ q*fixedScale ≤ (I.hi : ℚ))

theorem rationalCheck_sound {I : FixedBox} {q : ℚ} (h : I.rationalCheck q = true) :
    (q : ℝ) ∈ I := by
  simp only [rationalCheck, decide_eq_true_eq] at h
  change (I.lo : ℝ) ≤ (q : ℝ)*fixedScale ∧ (q : ℝ)*fixedScale ≤ (I.hi : ℝ)
  exact_mod_cast h

def coefficientsCheck : List ℚ → List FixedBox → Bool
  | [], [] => true
  | q::qs, I::Is => I.rationalCheck q && coefficientsCheck qs Is
  | _, _ => false

theorem coefficientsCheck_sound {qs : List ℚ} {Is : List FixedBox}
    (h : coefficientsCheck qs Is = true) : List.Forall₂ (fun (q : ℚ) (I : FixedBox) => (q : ℝ) ∈ I) qs Is := by
  induction qs generalizing Is with
  | nil =>
    cases Is with
    | nil => exact List.Forall₂.nil
    | cons I Is => simp [coefficientsCheck] at h
  | cons q qs ih =>
    cases Is with
    | nil => simp [coefficientsCheck] at h
    | cons I Is =>
      simp only [coefficientsCheck, Bool.and_eq_true] at h
      exact List.Forall₂.cons (rationalCheck_sound h.1) (ih h.2)

def hornerBoxes (I : FixedBox) : List FixedBox → FixedBox
  | [] => ofRat 0
  | c::cs => c.add (I.mul (hornerBoxes I cs))

theorem mem_hornerBoxes {x : ℝ} {I : FixedBox} (hx : x ∈ I)
    {qs : List ℚ} {Is : List FixedBox} (h : List.Forall₂ (fun (q : ℚ) (J : FixedBox) => (q : ℝ) ∈ J) qs Is) :
    IntervalRat.hornerVal qs x ∈ hornerBoxes I Is := by
  induction h with
  | nil => simpa [hornerBoxes, IntervalRat.hornerVal] using mem_ofRat 0
  | cons hhead htail ih => exact mem_add hhead (mem_mul hx ih)

def intervalCheck (J : FixedBox) (I : IntervalRat) : Bool :=
  decide ((J.lo : ℚ) ≤ I.lo*fixedScale ∧ I.hi*fixedScale ≤ (J.hi : ℚ))

theorem intervalCheck_sound {J : FixedBox} {I : IntervalRat}
    (h : J.intervalCheck I = true) {x : ℝ} (hx : x ∈ I) : x ∈ J := by
  simp only [intervalCheck, decide_eq_true_eq] at h
  have hl : (J.lo : ℝ) ≤ (I.lo : ℝ)*fixedScale := by exact_mod_cast h.1
  have hh : (I.hi : ℝ)*fixedScale ≤ (J.hi : ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right hx.1 fixedScale_real_pos.le),
    (mul_le_mul_of_nonneg_right hx.2 fixedScale_real_pos.le).trans hh⟩

def cosCoefficients32 : List FixedBox := [
  ⟨340282366920938463463374607431768211456, 340282366920938463463374607431768211456⟩,
  ⟨0, 0⟩,
  ⟨-170141183460469231731687303715884105728, -170141183460469231731687303715884105728⟩,
  ⟨0, 0⟩,
  ⟨14178431955039102644307275309657008810, 14178431955039102644307275309657008811⟩,
  ⟨0, 0⟩,
  ⟨-472614398501303421476909176988566961, -472614398501303421476909176988566960⟩,
  ⟨0, 0⟩,
  ⟨8439542830380418240659092446224410, 8439542830380418240659092446224411⟩,
  ⟨0, 0⟩,
  ⟨-93772698115337980451767693846938, -93772698115337980451767693846937⟩,
  ⟨0, 0⟩,
  ⟨710399228146499851907331013991, 710399228146499851907331013992⟩,
  ⟨0, 0⟩,
  ⟨-3903292462343405779710609967, -3903292462343405779710609966⟩,
  ⟨0, 0⟩,
  ⟨16263718593097524082127541, 16263718593097524082127542⟩,
  ⟨0, 0⟩,
  ⟨-53149407166985372817411, -53149407166985372817410⟩,
  ⟨0, 0⟩,
  ⟨139866860965750981098, 139866860965750981099⟩,
  ⟨0, 0⟩,
  ⟨-302742123302491302, -302742123302491301⟩,
  ⟨0, 0⟩,
  ⟨548445875547991, 548445875547992⟩,
  ⟨0, 0⟩,
  ⟨-843762885459, -843762885458⟩,
  ⟨0, 0⟩,
  ⟨1116088472, 1116088473⟩,
  ⟨0, 0⟩,
  ⟨-1282861, -1282860⟩,
  ⟨0, 0⟩,
  ⟨1293, 1294⟩]

theorem cosCoefficients32_correct :
    List.Forall₂ (fun (q : ℚ) (I : FixedBox) => (q : ℝ) ∈ I) (IntervalRat.cosTaylorCoeffs 32) cosCoefficients32 := by
  apply coefficientsCheck_sound
  decide +kernel

def sinCoefficients32 : List FixedBox := [
  ⟨0, 0⟩,
  ⟨340282366920938463463374607431768211456, 340282366920938463463374607431768211456⟩,
  ⟨0, 0⟩,
  ⟨-56713727820156410577229101238628035243, -56713727820156410577229101238628035242⟩,
  ⟨0, 0⟩,
  ⟨2835686391007820528861455061931401762, 2835686391007820528861455061931401763⟩,
  ⟨0, 0⟩,
  ⟨-67516342643043345925272739569795281, -67516342643043345925272739569795280⟩,
  ⟨0, 0⟩,
  ⟨937726981153379804517676938469378, 937726981153379804517676938469379⟩,
  ⟨0, 0⟩,
  ⟨-8524790737757998222887972167904, -8524790737757998222887972167903⟩,
  ⟨0, 0⟩,
  ⟨54646094472807680915948539537, 54646094472807680915948539538⟩,
  ⟨0, 0⟩,
  ⟨-260219497489560385314040665, -260219497489560385314040664⟩,
  ⟨0, 0⟩,
  ⟨956689329005736710713384, 956689329005736710713385⟩,
  ⟨0, 0⟩,
  ⟨-2797337219315019621969, -2797337219315019621968⟩,
  ⟨0, 0⟩,
  ⟨6660326712654808623, 6660326712654808624⟩,
  ⟨0, 0⟩,
  ⟨-13162701013151796, -13162701013151795⟩,
  ⟨0, 0⟩,
  ⟨21937835021919, 21937835021920⟩,
  ⟨0, 0⟩,
  ⟨-31250477240, -31250477239⟩,
  ⟨0, 0⟩,
  ⟨38485809, 38485810⟩,
  ⟨0, 0⟩,
  ⟨-41383, -41382⟩,
  ⟨0, 0⟩]

theorem sinCoefficients32_correct :
    List.Forall₂ (fun (q : ℚ) (I : FixedBox) => (q : ℝ) ∈ I) (IntervalRat.sinTaylorCoeffs 32) sinCoefficients32 := by
  apply coefficientsCheck_sound
  decide +kernel

def remainder32 : FixedBox := ⟨-2891568412417722264002, 2891568412417722264002⟩

theorem remainder32_cos_correct :
    remainder32.intervalCheck (IntervalRat.cosRemainderBoundComputable trigDomain 32) = true := by
  decide +kernel

theorem remainder32_sin_correct :
    remainder32.intervalCheck (IntervalRat.sinRemainderBoundComputable trigDomain 32) = true := by
  decide +kernel

def smallCos32 (I : FixedBox) : FixedBox := (I.hornerBoxes cosCoefficients32).add remainder32

def smallSin32 (I : FixedBox) : FixedBox := (I.hornerBoxes sinCoefficients32).add remainder32

theorem mem_smallCos32 {x : ℝ} {I : FixedBox} (hx : x ∈ I) (hd : x ∈ trigDomain) :
    Real.cos x ∈ I.smallCos32 := by
  have hp := mem_hornerBoxes hx cosCoefficients32_correct
  have hr := intervalCheck_sound remainder32_cos_correct
    (IntervalRat.cos_taylor_remainder_in_interval hd 32)
  rw [IntervalRat.taylorSeries_cos_eq_horner] at hr
  have h := mem_add hp hr
  convert! h using 1
  ring

theorem mem_smallSin32 {x : ℝ} {I : FixedBox} (hx : x ∈ I) (hd : x ∈ trigDomain) :
    Real.sin x ∈ I.smallSin32 := by
  have hp := mem_hornerBoxes hx sinCoefficients32_correct
  have hr := intervalCheck_sound remainder32_sin_correct
    (IntervalRat.sin_taylor_remainder_in_interval hd 32)
  rw [IntervalRat.taylorSeries_sin_eq_horner] at hr
  have h := mem_add hp hr
  convert! h using 1
  ring

def cos32 (I : FixedBox) : FixedBox :=
  let J := I.reduced
  if -4*fixedScale ≤ J.lo ∧ J.hi ≤ 4*fixedScale then J.smallCos32 else unit

def sin32 (I : FixedBox) : FixedBox :=
  let J := I.reduced
  if -4*fixedScale ≤ J.lo ∧ J.hi ≤ 4*fixedScale then J.smallSin32 else unit

theorem mem_cos32 {x : ℝ} {I : FixedBox} (hx : x ∈ I) : Real.cos x ∈ I.cos32 := by
  have hr := mem_reduced hx
  have he : Real.cos x = Real.cos (x-2*Real.pi*(I.shiftIndex : ℝ)) := by
    have h := Real.cos_add_int_mul_two_pi x (-I.shiftIndex)
    convert h.symm using 1 <;> congr 1 <;> push_cast <;> ring
  unfold cos32
  dsimp only []
  split_ifs with hb
  · rw [he]
    exact mem_smallCos32 hr (mem_trigDomain_of_bounds hr hb)
  · exact mem_unit ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

theorem mem_sin32 {x : ℝ} {I : FixedBox} (hx : x ∈ I) : Real.sin x ∈ I.sin32 := by
  have hr := mem_reduced hx
  have he : Real.sin x = Real.sin (x-2*Real.pi*(I.shiftIndex : ℝ)) := by
    have h := Real.sin_add_int_mul_two_pi x (-I.shiftIndex)
    convert h.symm using 1 <;> congr 1 <;> push_cast <;> ring
  unfold sin32
  dsimp only []
  split_ifs with hb
  · rw [he]
    exact mem_smallSin32 hr (mem_trigDomain_of_bounds hr hb)
  · exact mem_unit ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩


end
end ErdosOverlap.Numerics.FixedBox
