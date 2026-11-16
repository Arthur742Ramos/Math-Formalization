module

public import LeanCert.Core.IntervalRat.TrigReduced
public import LeanCert.Core.IntervalDyadic
public import Mathlib.Tactic.NormNum

/-!
# Kernel-only trigonometric enclosures

This module uses the proved interval soundness theorems of the pinned LeanCert
dependency. Concrete certificate predicates are evaluated by the Lean kernel;
no native-evaluation axiom or external interval report is used.
-/

namespace ErdosOverlap.Numerics

open LeanCert.Core

public section

/-- An outward dyadic enclosure of an exact rational number. -/
@[expose] def rationalDyadic (q : ℚ) (precision : ℤ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) precision

theorem mem_rationalDyadic (q : ℚ) (precision : ℤ) (hp : precision ≤ 0) :
    (q : ℝ) ∈ rationalDyadic q precision :=
  IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton q) precision hp

/-- A finite rational enclosure test for cosine at a rational argument. -/
@[expose] def cosineCheck (x lo hi : ℚ) (degree : ℕ) : Bool :=
  let enclosure := IntervalRat.cosComputableReduced (IntervalRat.singleton x) degree
  decide (lo ≤ enclosure.lo ∧ enclosure.hi ≤ hi)

/-- A finite rational enclosure test for sine at a rational argument. -/
@[expose] def sineCheck (x lo hi : ℚ) (degree : ℕ) : Bool :=
  let enclosure := IntervalRat.sinComputableReduced (IntervalRat.singleton x) degree
  decide (lo ≤ enclosure.lo ∧ enclosure.hi ≤ hi)

theorem cosineCheck_sound {x lo hi : ℚ} {degree : ℕ}
    (h : cosineCheck x lo hi degree = true) :
    (lo : ℝ) ≤ Real.cos (x : ℝ) ∧ Real.cos (x : ℝ) ≤ (hi : ℝ) := by
  have hm := IntervalRat.mem_cosComputableReduced (IntervalRat.mem_singleton x) degree
  simp only [cosineCheck, decide_eq_true_eq] at h
  constructor
  · exact (Rat.cast_le.mpr h.1).trans hm.1
  · exact hm.2.trans (Rat.cast_le.mpr h.2)

theorem sineCheck_sound {x lo hi : ℚ} {degree : ℕ}
    (h : sineCheck x lo hi degree = true) :
    (lo : ℝ) ≤ Real.sin (x : ℝ) ∧ Real.sin (x : ℝ) ≤ (hi : ℝ) := by
  have hm := IntervalRat.mem_sinComputableReduced (IntervalRat.mem_singleton x) degree
  simp only [sineCheck, decide_eq_true_eq] at h
  constructor
  · exact (Rat.cast_le.mpr h.1).trans hm.1
  · exact hm.2.trans (Rat.cast_le.mpr h.2)

/-- Range-reduced cosine with explicit outward dyadic rounding. -/
@[expose] def cosDyadic (I : IntervalDyadic) (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (IntervalRat.cosComputableReduced I.toIntervalRat degree) precision

/-- Range-reduced sine with explicit outward dyadic rounding. -/
@[expose] def sinDyadic (I : IntervalDyadic) (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (IntervalRat.sinComputableReduced I.toIntervalRat degree) precision

theorem mem_cosDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    Real.cos x ∈ cosDyadic I degree precision := by
  exact IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.mem_cosComputableReduced (IntervalDyadic.mem_toIntervalRat.mp hx) degree)
    precision hp

theorem mem_sinDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    Real.sin x ∈ sinDyadic I degree precision := by
  exact IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.mem_sinComputableReduced (IntervalDyadic.mem_toIntervalRat.mp hx) degree)
    precision hp

/-- A kernel-checked enclosure at the first frequency of the native6 kernel.
This is an arithmetic fixture, not the complete integral certificate. -/
theorem native6_first_cosine_enclosure :
    (9416 : ℝ)/10000 ≤ Real.cos ((2970005434023 : ℝ)/500000000000) ∧
      Real.cos ((2970005434023 : ℝ)/500000000000) ≤ (9418 : ℝ)/10000 := by
  have h : cosineCheck (2970005434023/500000000000) (9416/10000) (9418/10000) 30 = true := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using cosineCheck_sound h

end
end ErdosOverlap.Numerics
