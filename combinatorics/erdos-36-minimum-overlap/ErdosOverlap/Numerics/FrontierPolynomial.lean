/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierPolynomialData
public import ErdosOverlap.Certificate.Native6Grid.UniformError
public import ErdosOverlap.Certificate.FrontierGrid.UniformError
public import ErdosOverlap.Certificate.FrontierTrigIdentities

namespace ErdosOverlap.FrontierGrid
open Numerics
public section

theorem combined_cosine_uniform_error (j : ℕ) (hj : j < 1024) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum FrontierTrig.terms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ)*u) -
      polynomialValue (combinedCoefficients j) u| ≤ (2 / 1000000000000 : ℝ) := by
  rw [FrontierTrig.sum_eq_old_add_corrections, combinedCoefficients,
    polynomialValue_addPolynomialCoefficients]
  have hold := Native6Grid.cosine_uniform_error j hj hu
  have hnew := cosine_uniform_error j hj hu
  have htriangle := abs_add_le
    (cosineSum Native6Trig.terms ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ)*u) -
      polynomialValue (quantizedCoefficients (Native6Grid.coefficientRow j)) u)
    (cosineSum FrontierTrig.correctionTerms ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ)*u) -
      polynomialValue (quantizedCoefficients (coefficientRow j)) u)
  rw [show cosineSum Native6Trig.terms ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ)*u) -
        polynomialValue (quantizedCoefficients (Native6Grid.coefficientRow j)) u +
      (cosineSum FrontierTrig.correctionTerms ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ)*u) -
        polynomialValue (quantizedCoefficients (coefficientRow j)) u) =
      cosineSum Native6Trig.terms ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ)*u) +
        cosineSum FrontierTrig.correctionTerms ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ)*u) -
        (polynomialValue (quantizedCoefficients (Native6Grid.coefficientRow j)) u +
          polynomialValue (quantizedCoefficients (coefficientRow j)) u) by ring] at htriangle
  linarith

theorem combined_cosine_uniform_error_at (j : ℕ) (hj : j < 1024) {t : ℝ}
    (ht : |(t-(taylorGridCenter j : ℝ))/(taylorGridRadius : ℝ)| ≤ 1) :
    |cosineSum FrontierTrig.terms t - polynomialValue (combinedCoefficients j)
      ((t-(taylorGridCenter j : ℝ))/(taylorGridRadius : ℝ))| ≤
      (2 / 1000000000000 : ℝ) := by
  have he : (taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ)*
      ((t-(taylorGridCenter j : ℝ))/(taylorGridRadius : ℝ)) = t := by
    have hr : (taylorGridRadius : ℝ) ≠ 0 := by norm_num [taylorGridRadius]
    field_simp [hr]
    ring
  simpa only [he] using combined_cosine_uniform_error j hj ht

theorem combined_cosine_uniform_error_on_interval (j : ℕ) (hj : j < 1024) {t : ℝ}
    (ht : t ∈ Set.Icc ((taylorGridCenter j : ℝ)-(taylorGridRadius : ℝ))
      ((taylorGridCenter j : ℝ)+(taylorGridRadius : ℝ))) :
    |cosineSum FrontierTrig.terms t - polynomialValue (combinedCoefficients j)
      ((t-(taylorGridCenter j : ℝ))/(taylorGridRadius : ℝ))| ≤
      (2 / 1000000000000 : ℝ) := by
  apply combined_cosine_uniform_error_at j hj
  have hr : (0 : ℝ) < taylorGridRadius := by norm_num [taylorGridRadius]
  rw [abs_div, abs_of_pos hr]
  apply (div_le_one hr).mpr
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

end
end ErdosOverlap.FrontierGrid
