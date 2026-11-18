module

public import BoundedEdgeRegularSubgraphs.Incidence
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Ring

/-!
# Fourier inversion for degree atoms

The phase space has normalized Haar measure. With period 2π this absorbs
the factor (2π)⁻ᵏ in the manuscript's inversion formula.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

abbrev PhaseCircle := AddCircle (2 * Real.pi)

instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

variable {α : Type*} [Fintype α]

/-- Product of normalized Haar measures on the phase coordinates. -/
noncomputable def phaseLaw : Measure (α → PhaseCircle) :=
  Measure.pi (fun _ ↦ AddCircle.haarAddCircle)

/-- Product of the one-coordinate integer characters. -/
noncomputable def latticeCharacter (r : α → ℤ) (t : α → PhaseCircle) : ℂ :=
  ∏ i, fourier (r i) (t i)

private theorem latticeCharacter_add (r s : α → ℤ) (t : α → PhaseCircle) :
    latticeCharacter (r + s) t = latticeCharacter r t * latticeCharacter s t := by
  simp only [latticeCharacter, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

private theorem latticeCharacter_sum {ι : Type*} (A : Finset ι) (r : ι → α → ℤ)
    (t : α → PhaseCircle) :
    latticeCharacter (∑ e ∈ A, r e) t = ∏ e ∈ A, latticeCharacter (r e) t := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [latticeCharacter]
  | insert e A he ih =>
    rw [Finset.sum_insert he, Finset.prod_insert he, latticeCharacter_add, ih]

private theorem norm_latticeCharacter (r : α → ℤ) (t : α → PhaseCircle) :
    ‖latticeCharacter r t‖ = 1 := by
  simp [latticeCharacter, norm_prod]

private theorem integral_circle_fourier (n : ℤ) :
    ∫ t : PhaseCircle, fourier n t ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right hn]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hn (Fact.out : 0 < 2 * Real.pi))

private theorem integral_latticeCharacter (r : α → ℤ) :
    ∫ t, latticeCharacter r t ∂phaseLaw = if r = 0 then 1 else 0 := by
  classical
  unfold phaseLaw latticeCharacter
  rw [integral_fintype_prod_eq_prod (fun i t ↦ fourier (r i) t)]
  simp_rw [integral_circle_fourier]
  by_cases hr : r = 0
  · subst r
    simp
  · rw [ite_eq_right hr]
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      contrapose! hr
      exact funext hr
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

variable [LinearOrder α]

/-- The character contributed by a present edge. -/
noncomputable def edgeCharacter (e : Edge α) (t : α → PhaseCircle) : ℂ :=
  fourier 1 (t e.val.1) * fourier 1 (t e.val.2)

private theorem latticeCharacter_edgeIncidence (e : Edge α) (t : α → PhaseCircle) :
    latticeCharacter (edgeIncidence e) t = edgeCharacter e t := by
  classical
  have h (j : α) : (∏ i, fourier (if i = j then 1 else 0) (t i)) = fourier 1 (t j) := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  simp only [latticeCharacter, edgeIncidence, fourier_add, Finset.prod_mul_distrib,
    h, edgeCharacter]

/-- The centred degree character on all available edges. -/
noncomputable def degreeFourier (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1)
    (d : α → ℤ) (t : α → PhaseCircle) : ℂ :=
  latticeCharacter (-d) t *
    ∏ e ∈ A, (1 - ((p e : ℝ) : ℂ) + ((p e : ℝ) : ℂ) * edgeCharacter e t)

/-- The characteristic function of the degree vector is a product over independent edges. -/
theorem integral_degree_character (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → PhaseCircle) :
    ∫ w, latticeCharacter (degreeVector A w - d) t ∂graphLaw p = degreeFourier A p d t := by
  classical
  let f (e : Edge α) (x : ℝ) :=
    if e ∈ A then (if x = 1 then edgeCharacter e t else 1) else (1 : ℂ)
  have hfiltered : (Finset.univ.filter fun e : Edge α ↦ e ∈ A) = A := by
    ext e
    simp
  have h (w : Edge α → ℝ) :
      latticeCharacter (degreeVector A w - d) t =
        latticeCharacter (-d) t * ∏ e, f e (w e) := by
    rw [sub_eq_add_neg, degreeVector, latticeCharacter_add, latticeCharacter_sum, mul_comm]
    congr 1
    change _ = ∏ e : Edge α, if e ∈ A then (if w e = 1 then edgeCharacter e t else 1) else 1
    rw [← Finset.prod_filter, hfiltered]
    refine Finset.prod_congr rfl (fun e _ ↦ ?_)
    by_cases hwe : w e = 1
    · simp [sampledIncidence, hwe, latticeCharacter_edgeIncidence]
    · simp [sampledIncidence, hwe, latticeCharacter]
  simp_rw [h]
  rw [integral_const_mul, graphLaw, integral_fintype_prod_eq_prod f]
  unfold degreeFourier
  congr 1
  calc
    (∏ e, ∫ x, f e x ∂bernoulliMeasure (1 : ℝ) 0 (p e)) =
        ∏ e : Edge α, if e ∈ A then
          (1 - ((p e : ℝ) : ℂ) + ((p e : ℝ) : ℂ) * edgeCharacter e t) else 1 := by
      refine Finset.prod_congr rfl (fun e _ ↦ ?_)
      rw [integral_bernoulliMeasure]
      by_cases he : e ∈ A
      · simp [f, he, Complex.real_smul]
        ring
      · simp [f, he, Complex.real_smul]
    _ = _ := by rw [← Finset.prod_filter, hfiltered]

private theorem measurable_joint_character (A : Finset (Edge α)) (d : α → ℤ) :
    Measurable (fun x : (Edge α → ℝ) × (α → PhaseCircle) ↦
      latticeCharacter (degreeVector A x.1 - d) x.2) := by
  have hfourier : Measurable (fun x : ℤ × PhaseCircle ↦ fourier x.1 x.2) :=
    measurable_from_prod_countable_right (fun n ↦ (fourier n).continuous.measurable)
  unfold latticeCharacter
  refine Finset.measurable_prod _ (fun i _ ↦ ?_)
  have hm : Measurable (fun x : (Edge α → ℝ) × (α → PhaseCircle) ↦
      degreeVector A x.1 i - d i) :=
    ((measurable_pi_apply i).comp ((measurable_degreeVector A).comp measurable_fst)).sub_const _
  exact hfourier.comp (hm.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- Exact Fourier inversion for the full array and for every available edge set.
No floor or centring hypothesis is needed for this equality. -/
theorem probability_degreeAtom_eq_integral_degreeFourier (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) :
    ((graphLaw p).real (degreeAtom A d) : ℂ) =
      ∫ t, degreeFourier A p d t ∂phaseLaw := by
  classical
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  have : IsProbabilityMeasure (phaseLaw (α := α)) := by unfold phaseLaw; infer_instance
  have hi : Integrable
      (Function.uncurry fun w t ↦ latticeCharacter (degreeVector A w - d) t)
      ((graphLaw p).prod phaseLaw) := by
    refine Integrable.of_bound (measurable_joint_character A d).aestronglyMeasurable 1 ?_
    exact ae_of_all _ (fun _ ↦ (norm_latticeCharacter _ _).le)
  simp_rw [← integral_degree_character A p d]
  rw [← integral_integral_swap hi]
  simp_rw [integral_latticeCharacter]
  have hind (w : Edge α → ℝ) :
      (if degreeVector A w - d = 0 then (1 : ℂ) else 0) =
        (degreeAtom A d).indicator (fun _ ↦ (1 : ℂ)) w := by
    by_cases he : degreeVector A w = d <;> simp [degreeAtom, Set.indicator, sub_eq_zero, he]
  simp_rw [hind]
  rw [integral_indicator_const 1 (measurableSet_degreeAtom A d)]
  simp [Complex.real_smul]

end BoundedEdgeRegularSubgraphs
