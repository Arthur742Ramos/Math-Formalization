/- AI-assisted formalization under repository Apache-2.0.
Explicit bounds on the actual interval epigraph coordinates and
an algebraic obstruction to feasible rays. No active-basis, small-witness,
solver-complexity, or output-height theorem is asserted here. -/
module
public import RationalIntervalRealPoint
public import RationalIntervalRepertoire
public import RationalGapRealDecision
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_real_mass_coordinate_bound {m : ℕ} (q : Fin m → ℝ) (r : ℚ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = (r : ℝ)) (i : Fin m) :
    |q i| ≤ |(r : ℝ)| := by
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
    (Finset.mem_univ i)
  rw [hm] at hi
  exact (abs_of_nonneg (hq i)).le.trans (hi.trans (le_abs_self _))

theorem rational_gap_real_system_coordinate_bound {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (x : Fin m → ℝ)
    (hx : (rationalGapSystem K D p M r ρ η).RealSatisfies x) :
    ∀ i, |x i| ≤ |(r : ℝ)| := by
  have hq (i : Fin m) : 0 ≤ x i := by
    have hh := hx (.inl i)
    change (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*x j) ≤ ((0 : ℚ) : ℝ) at hh
    have he : (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*x j) = -x i := by
      calc
        _ = ∑ j, if j=i then -x j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j=i <;> simp [hj]
        _ = _ := by simp
    rw [he, Rat.cast_zero] at hh
    exact neg_nonpos.mp hh
  have hu := hx (.inr (.inl 0))
  have hl := hx (.inr (.inl 1))
  change (∑ j, ((1 : ℚ) : ℝ)*x j) ≤ (r : ℝ) at hu
  change (∑ j, ((-1 : ℚ) : ℝ)*x j) ≤ ((-r : ℚ) : ℝ) at hl
  have hu' : (∑ j, x j) ≤ (r : ℝ) := by simpa using hu
  have hl' : (r : ℝ) ≤ ∑ j, x j := by
    simpa only [Rat.cast_neg, Rat.cast_one, neg_one_mul, Finset.sum_neg_distrib,
      neg_le_neg_iff] using hl
  exact rational_real_mass_coordinate_bound x r hq (le_antisymm hu' hl')

theorem rational_gap_append_real_coordinate_bound {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x) :
    ∀ i, |x i| ≤ |(r : ℝ)| :=
  rational_gap_real_system_coordinate_bound K D p M r ρ η x
    (((rational_linear_real_append_iff _ R x).mp hx).1)

/-- These radii are finite expressions in the literal input intervals and
the literal generated envelope rows. No proposed output-height budget occurs. -/
def rationalIntervalCoordinateRadius {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ)
    (M r η : ℚ) : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ :=
  intervalVariableEncode (Sum.elim (fun _ => |(r : ℝ)|)
    (Sum.elim (fun v => (|(lo v.1 v.2 : ℝ)|+|(hi v.1 v.2 : ℝ)|)*|(r : ℝ)|)
      (Sum.elim (fun v => |(loK v.1 v.2 : ℝ)|+|(hiK v.1 v.2 : ℝ)|)
        (fun v => |(rationalEnvelope M r (M*r-rationalGridNode M r η (v.1.val+1)) : ℝ)|))))

theorem rational_interval_real_point_block_bounds {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ)
    (V : Fin m → Fin k → ℝ) (K : Fin k → Fin k → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℝ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℝ)
    (h : RationalIntervalRealPoint loK hiK lo hi V K p q M r ρ η A) :
    (∀ i, |q i| ≤ |(r : ℝ)|) ∧
    (∀ i a, |V i a| ≤ (|(lo i a : ℝ)|+|(hi i a : ℝ)|)*|(r : ℝ)|) ∧
    (∀ a b, |K a b| ≤ |(loK a b : ℝ)|+|(hiK a b : ℝ)|) ∧
    ∀ l i, |A l i| ≤
      |(rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1)) : ℝ)| := by
  rcases h with ⟨hq,hm,hV,_hK,hKb,_ha,_hlo,_hcap,hA⟩
  have hqb := rational_real_mass_coordinate_bound q r hq hm
  refine ⟨hqb,?_,?_,?_⟩
  · intro i a
    have hl := neg_abs_le (lo i a : ℝ)
    have hu := le_abs_self (hi i a : ℝ)
    have hll := mul_le_mul_of_nonneg_right hl (hq i)
    have huu := mul_le_mul_of_nonneg_right hu (hq i)
    have hqabs : q i ≤ |(r : ℝ)| := (le_abs_self _).trans (hqb i)
    have hscale := mul_le_mul_of_nonneg_left hqabs
      (add_nonneg (abs_nonneg (lo i a : ℝ)) (abs_nonneg (hi i a : ℝ)))
    have hloextra := mul_nonneg (abs_nonneg (lo i a : ℝ)) (hq i)
    have hhiextra := mul_nonneg (abs_nonneg (hi i a : ℝ)) (hq i)
    exact abs_le.mpr ⟨by nlinarith [(hV i a).1], by nlinarith [(hV i a).2]⟩
  · intro a b
    have hl := neg_abs_le (loK a b : ℝ)
    have hu := le_abs_self (hiK a b : ℝ)
    exact abs_le.mpr ⟨by linarith [(hKb a b).1, abs_nonneg (hiK a b : ℝ)],
      by linarith [(hKb a b).2, abs_nonneg (loK a b : ℝ)]⟩
  · intro l i
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => (hA l).1 j) (Finset.mem_univ i)
    rw [abs_of_nonneg ((hA l).1 i)]
    exact hi.trans ((hA l).2.2.trans (le_abs_self _))

theorem rational_interval_system_coordinate_radius {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (M r ρ η : ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ)
    (hx : (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x) :
    ∀ u, |x u| ≤ rationalIntervalCoordinateRadius loK hiK lo hi M r η u := by
  obtain ⟨hq,hV,hK,hA⟩ := rational_interval_real_point_block_bounds loK hiK lo hi
    (intervalV x) (intervalK x) p (intervalQ x) M r ρ η (intervalAux x)
    ((rational_interval_system_real_point loK hiK lo hi p M r ρ η x).mp hx)
  intro u
  obtain ⟨v,rfl⟩ := (rationalIntervalVariableEquiv k m (rationalGridSize M r η)).surjective u
  dsimp only [rationalIntervalCoordinateRadius, intervalVariableEncode]
  rw [(rationalIntervalVariableEquiv k m (rationalGridSize M r η)).symm_apply_apply]
  rcases v with i | v
  · exact hq i
  · rcases v with v | v
    · exact hV v.1 v.2
    · rcases v with v | v
      · exact hK v.1 v.2
      · exact hA v.1 v.2

theorem rational_interval_repertoire_coordinate_radius {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ)
    (hx : (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    ∀ u, |x u| ≤ rationalIntervalCoordinateRadius loK hiK lo hi M r η u :=
  rational_interval_system_coordinate_radius loK hiK lo hi p M r ρ η x
    (((rational_interval_repertoire_real_system_iff loK hiK lo hi p M r ρ η R x).mp hx).1)

/-- A bounded real feasible set has no nonconstant feasible ray. This uses
only finite linear expressions and ordered-field algebra. -/
theorem rational_lp_bounded_no_feasible_direction {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (U : Fin n → ℝ)
    (hb : ∀ y, S.RealSatisfies y → ∀ j, |y j| ≤ U j)
    (x v : Fin n → ℝ) (hx : S.RealSatisfies x)
    (hv : ∀ row, (∑ j, (S.coefficient row j : ℝ)*v j) ≤ 0) : v = 0 := by
  have hray (t : ℝ) (ht : 0 ≤ t) : S.RealSatisfies (fun j => x j+t*v j) := by
    intro row
    have he : (∑ j, (S.coefficient row j : ℝ)*(x j+t*v j)) =
        (∑ j, (S.coefficient row j : ℝ)*x j)+t*(∑ j, (S.coefficient row j : ℝ)*v j) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht (hv row))).trans (hx row)
  funext j
  by_contra hj
  have ha : 0 < |v j| := abs_pos.mpr hj
  have hU : 0 ≤ U j := (abs_nonneg (x j)).trans (hb x hx j)
  let t := (U j+|x j|+1)/|v j|
  have ht : 0 ≤ t := div_nonneg (by positivity) (le_of_lt ha)
  have hmul : t*|v j| = U j+|x j|+1 := div_mul_cancel₀ _ (ne_of_gt ha)
  have htri := abs_add_le (x j+t*v j) (-x j)
  have he : (x j+t*v j)+ -x j = t*v j := by ring
  rw [he, abs_neg, abs_mul, abs_of_nonneg ht] at htri
  have hy := hb _ (hray t ht) j
  linarith

theorem rational_lp_bounded_nonzero_direction_positive_row {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (U : Fin n → ℝ)
    (hb : ∀ y, S.RealSatisfies y → ∀ j, |y j| ≤ U j)
    (x v : Fin n → ℝ) (hx : S.RealSatisfies x) (hv : v ≠ 0) :
    ∃ row, 0 < ∑ j, (S.coefficient row j : ℝ)*v j := by
  by_contra h
  push Not at h
  exact hv (rational_lp_bounded_no_feasible_direction S U hb x v hx h)

end SparseCompletion
