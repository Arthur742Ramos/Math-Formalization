/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.GridSoundness
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness
public import ErdosOverlap.Certificate.Native6Grid.FactorChecks
public import ErdosOverlap.Certificate.Native6Grid.RemainderChecks

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem cosine_uniform_error (j : ℕ) (hj : j < 1024) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum Native6Trig.terms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) * u) -
      polynomialValue (quantizedCoefficients (coefficientRow j)) u| ≤
      (1 / 1000000000000 : ℝ) := by
  exact completeCoefficientRowCheck_sound factorRows_correct (trigRows_correct j hj)
    (coefficientRows_checked j hj) remainder_checked hu

theorem cosine_uniform_error_at (j : ℕ) (hj : j < 1024) {t : ℝ}
    (ht : |(t - (taylorGridCenter j : ℝ)) / (taylorGridRadius : ℝ)| ≤ 1) :
    |cosineSum Native6Trig.terms t -
      polynomialValue (quantizedCoefficients (coefficientRow j))
        ((t - (taylorGridCenter j : ℝ)) / (taylorGridRadius : ℝ))| ≤
      (1 / 1000000000000 : ℝ) := by
  have he : (taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) *
      ((t - (taylorGridCenter j : ℝ)) / (taylorGridRadius : ℝ)) = t := by
    have hr : (taylorGridRadius : ℝ) ≠ 0 := by norm_num [taylorGridRadius]
    field_simp [hr]
    ring
  simpa only [he] using cosine_uniform_error j hj ht

theorem cosine_uniform_error_on_interval (j : ℕ) (hj : j < 1024) {t : ℝ}
    (ht : t ∈ Set.Icc ((taylorGridCenter j : ℝ) - (taylorGridRadius : ℝ))
      ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ))) :
    |cosineSum Native6Trig.terms t -
      polynomialValue (quantizedCoefficients (coefficientRow j))
        ((t - (taylorGridCenter j : ℝ)) / (taylorGridRadius : ℝ))| ≤
      (1 / 1000000000000 : ℝ) := by
  apply cosine_uniform_error_at j hj
  have hr : (0 : ℝ) < taylorGridRadius := by norm_num [taylorGridRadius]
  rw [abs_div, abs_of_pos hr]
  apply (div_le_one hr).mpr
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

end
end ErdosOverlap.Native6Grid
