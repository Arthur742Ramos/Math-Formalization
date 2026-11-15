/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Certificate.OuterFrequencyData
public import ErdosOverlap.Numerics.SincEnclosure

/-!
# Kernel-checked sinc-square bounds for all 34 outer frequencies

The fixed-point enclosure is proved to contain the actual real sinc.
Only integer/rational computation is used to check the proposed upper
bounds, and the rational sine-bound conditions were checked separately.
-/

namespace ErdosOverlap.Outer180
open LeanCert.Core
open ErdosOverlap.Numerics
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def frequencySincCheck (r : OuterFrequencyData) : Bool :=
  let I := Numerics.sincBox r.frequency
  (I.mul I).upperBoundedBy r.cosineBound

theorem frequencySincCheck_sound (r : OuterFrequencyData)
    (hc : frequencySincCheck r = true) :
    Real.sinc (r.frequency : ℝ)^2 ≤ (r.cosineBound : ℝ) := by
  have hm := FixedBox.mem_mul (Numerics.sinc_mem_box r.frequency) (Numerics.sinc_mem_box r.frequency)
  exact FixedBox.upperBoundedBy_sound (by simpa only [pow_two] using hm) hc

theorem frequencies_sinc_checked : frequencies.all frequencySincCheck = true := by
  decide +kernel

/-- Every transcendental and rational premise of the physical frequency
schema is discharged for the actual outer certificate inputs. -/
theorem frequencies_valid : ∀ r ∈ frequencies, r.Valid := by
  intro r hr
  apply r.valid_of_checks
  · exact frequencySincCheck_sound r (List.all_eq_true.mp frequencies_sinc_checked r hr)
  · exact List.all_eq_true.mp frequencies_rational_checked r hr

end
end ErdosOverlap.Outer180
