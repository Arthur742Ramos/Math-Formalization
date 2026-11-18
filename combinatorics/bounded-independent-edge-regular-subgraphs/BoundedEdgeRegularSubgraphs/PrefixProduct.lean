module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Product bound for prefix events

A constraint exposed at coordinate i depends only on coordinates at most i.
Bounds on its individual sections multiply under the product law.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

universe u

/-- Apply the section bound at the last coordinate, then induct on the remaining prefix. -/
theorem measure_pi_prefix_le (n : ℕ) :
    ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
      (good : Fin n → (∀ i, Ω i) → Prop) (bound : Fin n → ENNReal),
      (∀ i, MeasurableSet {x | good i x}) →
      (∀ i x y, (∀ j, j ≤ i → x j = y j) → (good i x ↔ good i y)) →
      (∀ i x, μ i {z | good i (Function.update x i z)} ≤ bound i) →
      Measure.pi μ {x | ∀ i, good i x} ≤ ∏ i, bound i := by
  classical
  induction n with
  | zero =>
    intros
    simp
  | succ n ih =>
    intro Ω _ μ _ good bound hm hp hs
    let last := Fin.last n
    let e := MeasurableEquiv.piFinSuccAbove Ω last
    let μ' (i : Fin n) := μ (last.succAbove i)
    let z₀ := Classical.choice (nonempty_of_isProbabilityMeasure (μ last))
    let subGood (i : Fin n) (x : ∀ j, Ω (last.succAbove j)) :=
      good (last.succAbove i) (e.symm (z₀, x))
    have hlast (z : Ω last) (x : ∀ j, Ω (last.succAbove j)) : e.symm (z, x) last = z := by
      exact Fin.insertNth_apply_same last z x
    have hcoord (z : Ω last) (x : ∀ j, Ω (last.succAbove j)) (i : Fin n) :
        e.symm (z, x) (last.succAbove i) = x i := by
      exact Fin.insertNth_apply_succAbove last z x i
    have hprefix (i : Fin n) (z z' : Ω last) (x y : ∀ j, Ω (last.succAbove j))
        (hxy : ∀ j, j ≤ i → x j = y j) :
        good (last.succAbove i) (e.symm (z, x)) ↔
          good (last.succAbove i) (e.symm (z', y)) := by
      apply hp
      intro j hj
      have hne : j ≠ last := by
        intro h
        subst j
        exact Fin.succAbove_ne last i (le_antisymm (Fin.le_last _) hj)
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
      rw [hcoord, hcoord]
      exact hxy k ((Fin.strictMono_succAbove last).le_iff_le.mp hj)
    have hup (x : ∀ j, Ω (last.succAbove j)) (i : Fin n) (z : Ω (last.succAbove i)) :
        e.symm (z₀, Function.update x i z) =
          Function.update (e.symm (z₀, x)) (last.succAbove i) z := by
      funext j
      by_cases hj : j = last
      · subst j
        rw [hlast, Function.update_of_ne (Ne.symm (Fin.succAbove_ne last i)), hlast]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        rw [hcoord]
        by_cases hki : k = i
        · subst k
          rw [Function.update_self, Function.update_self]
        · have hne : last.succAbove k ≠ last.succAbove i :=
            (Fin.strictMono_succAbove last).injective.ne hki
          rw [Function.update_of_ne hki, Function.update_of_ne hne, hcoord]
    have huplast (x : ∀ j, Ω (last.succAbove j)) (z : Ω last) :
        e.symm (z, x) = Function.update (e.symm (z₀, x)) last z := by
      funext j
      by_cases hj : j = last
      · subst j
        rw [hlast, Function.update_self]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        rw [hcoord, Function.update_of_ne (Fin.succAbove_ne last k), hcoord]
    have hsubMeas (i : Fin n) : MeasurableSet {x | subGood i x} := by
      exact (hm (last.succAbove i)).preimage
        (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
    have hsub := ih (fun j ↦ Ω (last.succAbove j)) μ' subGood (fun i ↦ bound (last.succAbove i))
      hsubMeas (fun i x y hxy ↦ hprefix i z₀ z₀ x y hxy) (by
        intro i x
        change μ (last.succAbove i) {z | good (last.succAbove i)
          (e.symm (z₀, Function.update x i z))} ≤ bound (last.succAbove i)
        simp_rw [hup]
        exact hs (last.succAbove i) (e.symm (z₀, x)))
    let A : Set (∀ i, Ω i) := {x | ∀ i, good i x}
    let prior : Set (∀ j, Ω (last.succAbove j)) := {x | ∀ i, subGood i x}
    have hA : MeasurableSet A := by
      have heq : A = ⋂ i, {x | good i x} := by
        ext x
        simp [A]
      rw [heq]
      exact MeasurableSet.iInter hm
    have hprior : MeasurableSet prior := by
      have heq : prior = ⋂ i, {x | subGood i x} := by
        ext x
        simp [prior]
      rw [heq]
      exact MeasurableSet.iInter hsubMeas
    have htransfer := (measurePreserving_piFinSuccAbove μ last).symm e
    change Measure.pi μ A ≤ ∏ i, bound i
    rw [← htransfer.measure_preimage hA.nullMeasurableSet,
      Measure.prod_apply_symm (hA.preimage e.symm.measurable)]
    calc
      _ ≤ ∫⁻ x, prior.indicator (fun _ ↦ bound last) x ∂Measure.pi μ' := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ prior
        · rw [Set.indicator_of_mem hx]
          refine (measure_mono (fun z hz ↦ ?_)).trans (hs last (e.symm (z₀, x)))
          change good last (Function.update (e.symm (z₀, x)) last z)
          rw [← huplast]
          exact (show ∀ i, good i (e.symm (z, x)) from hz) last
        · rw [Set.indicator_of_notMem hx]
          have hempty : (fun z ↦ (z, x)) ⁻¹' (e.symm ⁻¹' A) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            apply hx
            intro i
            exact (hprefix i z z₀ x x (fun _ _ ↦ rfl)).mp
              ((show ∀ j, good j (e.symm (z, x)) from hz) (last.succAbove i))
          change μ last ((fun z ↦ (z, x)) ⁻¹' (e.symm ⁻¹' A)) ≤ 0
          rw [hempty, measure_empty]
      _ = bound last * Measure.pi μ' prior := lintegral_indicator_const hprior _
      _ ≤ bound last * ∏ i, bound (last.succAbove i) := mul_le_mul_of_nonneg_left hsub bot_le
      _ = _ := (Fin.prod_univ_succAbove bound last).symm

/-- Grouping coordinates by their first index preserves the product law. -/
theorem measurePreserving_piCurry {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] (μ : ∀ i j, Measure (X i j))
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi (fun p : Sigma κ ↦ μ p.1 p.2))
      (Measure.pi (fun i ↦ Measure.pi (μ i))) := by
  classical
  let e := MeasurableEquiv.piCurry X
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro S hS
  rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hS)]
  have hrect : e.symm ⁻¹' Set.univ.pi S = Set.univ.pi (fun i ↦ Set.univ.pi (fun j ↦ S ⟨i,j⟩)) := by
    ext x
    simp [e, MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry, Sigma.forall]
  rw [hrect]
  simp_rw [Measure.pi_pi]
  exact Fintype.prod_sigma (fun p : Sigma κ ↦ μ p.1 p.2 (S p)) |>.symm

end BoundedEdgeRegularSubgraphs
