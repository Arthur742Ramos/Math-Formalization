/- AI-assisted formalization under repository Apache-2.0.
Finite active-row argument for a coordinate-bounded
feasible rational linear system. No topology, solver implementation, supplied
basis, small-witness height, or runtime theorem is asserted. -/
module
public import RationalLPBoxDomain
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalLPRealResponse {I : Type*} {n : ℕ} (S : RationalLinearSystem I n)
    (x : Fin n → ℝ) (row : I) : ℝ := ∑ j, (S.coefficient row j : ℝ)*x j

theorem rational_lp_real_response_step {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (x v : Fin n → ℝ) (t : ℝ) (row : I) :
    rationalLPRealResponse S (fun j => x j+t*v j) row =
      rationalLPRealResponse S x row+t*rationalLPRealResponse S v row := by
  unfold rationalLPRealResponse
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def rationalLPActiveRows {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (x : Fin n → ℝ) : Finset I := by
  classical
  exact Finset.univ.filter (fun row => rationalLPRealResponse S x row = (S.rightSide row : ℝ))

theorem rational_lp_active_row_mem {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (x : Fin n → ℝ) (row : I) :
    row ∈ rationalLPActiveRows S x ↔
      rationalLPRealResponse S x row = (S.rightSide row : ℝ) := by
  classical
  simp only [rationalLPActiveRows, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Finite selection over subsets of the original row family; no point
enumerator or LP solver is introduced. -/
theorem rational_lp_maximal_active_count {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (hf : ∃ x, S.RealSatisfies x) :
    ∃ x, S.RealSatisfies x ∧ ∀ y, S.RealSatisfies y →
      (rationalLPActiveRows S y).card ≤ (rationalLPActiveRows S x).card := by
  classical
  let candidates : Finset (Finset I) := Finset.univ.filter
    (fun a => ∃ x, S.RealSatisfies x ∧ rationalLPActiveRows S x = a)
  have hmem (x : Fin n → ℝ) (hx : S.RealSatisfies x) : rationalLPActiveRows S x ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x,hx,rfl⟩
  obtain ⟨x₀,hx₀⟩ := hf
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_,hmem x₀ hx₀⟩
  obtain ⟨x,hx,hax⟩ := (Finset.mem_filter.mp ha).2
  refine ⟨x,hx,?_⟩
  intro y hy
  rw [hax]
  exact hmax _ (hmem y hy)

/-- A nonzero vector in the kernel of every tight row permits a step to an
additional tight original row. The boundedness premise is geometric, and is
earned for the actual fixed/interval constructors in RationalLPBoxDomain. -/
theorem rational_lp_active_kernel_step {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (U : Fin n → ℝ)
    (hb : ∀ y, S.RealSatisfies y → ∀ j, |y j| ≤ U j)
    (x v : Fin n → ℝ) (hx : S.RealSatisfies x) (hv : v ≠ 0)
    (hker : ∀ row, rationalLPRealResponse S x row = (S.rightSide row : ℝ) →
      rationalLPRealResponse S v row = 0) :
    ∃ y, S.RealSatisfies y ∧
      (rationalLPActiveRows S x).card < (rationalLPActiveRows S y).card := by
  classical
  let positive : Finset I := Finset.univ.filter (fun row => 0 < rationalLPRealResponse S v row)
  have hp : positive.Nonempty := by
    obtain ⟨row,hr⟩ := rational_lp_bounded_nonzero_direction_positive_row S U hb x v hx hv
    exact ⟨row, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
  let ratio := fun row => ((S.rightSide row : ℝ)-rationalLPRealResponse S x row)/
    rationalLPRealResponse S v row
  obtain ⟨row,hrow,hmin⟩ := Finset.exists_min_image positive ratio hp
  have hpos : 0 < rationalLPRealResponse S v row := (Finset.mem_filter.mp hrow).2
  have hstrict : rationalLPRealResponse S x row < (S.rightSide row : ℝ) := by
    by_contra hn
    have he : rationalLPRealResponse S x row = (S.rightSide row : ℝ) :=
      le_antisymm (hx row) (le_of_not_gt hn)
    have hz := hker row he
    linarith
  let t := ratio row
  have ht : 0 < t := div_pos (sub_pos.mpr hstrict) hpos
  let y := fun j => x j+t*v j
  have hy : S.RealSatisfies y := by
    intro i
    change rationalLPRealResponse S y i ≤ (S.rightSide i : ℝ)
    rw [rational_lp_real_response_step]
    by_cases hi : 0 < rationalLPRealResponse S v i
    · have hmi := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      have hh : t*rationalLPRealResponse S v i ≤
          (S.rightSide i : ℝ)-rationalLPRealResponse S x i := (le_div_iff₀ hi).mp hmi
      linarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (le_of_not_gt hi)
      exact (add_le_of_nonpos_right hh).trans (hx i)
  have hsub : rationalLPActiveRows S x ⊆ rationalLPActiveRows S y := by
    intro i hi
    apply (rational_lp_active_row_mem S y i).mpr
    have he := (rational_lp_active_row_mem S x i).mp hi
    change rationalLPRealResponse S (fun j => x j+t*v j) i = _
    rw [rational_lp_real_response_step, hker i he, mul_zero, add_zero]
    exact he
  have hnew : row ∈ rationalLPActiveRows S y := by
    apply (rational_lp_active_row_mem S y row).mpr
    change rationalLPRealResponse S (fun j => x j+t*v j) row = _
    rw [rational_lp_real_response_step]
    have htrow : t*rationalLPRealResponse S v row =
        (S.rightSide row : ℝ)-rationalLPRealResponse S x row := div_mul_cancel₀ _ (ne_of_gt hpos)
    linarith
  have hold : row ∉ rationalLPActiveRows S x := by
    intro hi
    have he := (rational_lp_active_row_mem S x row).mp hi
    linarith
  refine ⟨y,hy,Finset.card_lt_card ?_⟩
  exact ⟨hsub, fun h => hold (h hnew)⟩

/-- The tight rows of an earned feasible point have trivial common kernel.
An active full-rank family is a conclusion, never a supplied field. -/
theorem rational_lp_exists_trivial_active_kernel {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (U : Fin n → ℝ)
    (hb : ∀ y, S.RealSatisfies y → ∀ j, |y j| ≤ U j)
    (hf : ∃ x, S.RealSatisfies x) :
    ∃ x, S.RealSatisfies x ∧ ∀ v : Fin n → ℝ,
      (∀ row, rationalLPRealResponse S x row = (S.rightSide row : ℝ) →
        rationalLPRealResponse S v row = 0) → v = 0 := by
  obtain ⟨x,hx,hmax⟩ := rational_lp_maximal_active_count S hf
  refine ⟨x,hx,?_⟩
  intro v hker
  by_contra hv
  obtain ⟨y,hy,hlt⟩ := rational_lp_active_kernel_step S U hb x v hx hv hker
  exact (not_lt_of_ge (hmax y hy)) hlt

theorem rational_gap_append_exists_trivial_active_kernel {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m)
    (hf : ∃ x, ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x) :
    let S := (rationalGapSystem K D p M r ρ η).append R
    ∃ x, S.RealSatisfies x ∧ ∀ v : Fin m → ℝ,
      (∀ row, rationalLPRealResponse S x row = (S.rightSide row : ℝ) →
        rationalLPRealResponse S v row = 0) → v = 0 :=
  rational_lp_exists_trivial_active_kernel _ (fun _ => |(r : ℝ)|)
    (fun x hx => rational_gap_append_real_coordinate_bound K D p M r ρ η R x hx) hf

theorem rational_interval_repertoire_exists_trivial_active_kernel
    {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hf : ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    let S := rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R
    ∃ x, S.RealSatisfies x ∧ ∀ v : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ,
      (∀ row, rationalLPRealResponse S x row = (S.rightSide row : ℝ) →
        rationalLPRealResponse S v row = 0) → v = 0 :=
  rational_lp_exists_trivial_active_kernel _ (rationalIntervalCoordinateRadius loK hiK lo hi M r η)
    (fun x hx => rational_interval_repertoire_coordinate_radius loK hiK lo hi p M r ρ η R x hx) hf

end SparseCompletion
