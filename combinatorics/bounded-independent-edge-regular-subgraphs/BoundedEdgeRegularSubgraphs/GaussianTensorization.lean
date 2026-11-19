module

public import BoundedEdgeRegularSubgraphs.GaussianProductParts
public import BoundedEdgeRegularSubgraphs.ProductVariance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Tensorizing the one-coordinate Gaussian variance bound
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem cons_update_tail {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    Fin.cons a (Function.update x i u) =
      Function.update (Fin.cons (α := fun _ ↦ ℝ) a x) i.succ u := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp only [Fin.cons_zero, Function.update_of_ne (Fin.succ_ne_zero i).symm]
  · by_cases h : j = i
    · subst j
      simp
    · have h' : j.succ ≠ i.succ := fun hh ↦ h (Fin.succ_inj.mp hh)
      simp only [Fin.cons_succ, Function.update_of_ne h, Function.update_of_ne h']

private theorem cons_update_head {n : ℕ} (a u : ℝ) (x : Fin n → ℝ) :
    Fin.cons u x = Function.update (Fin.cons (α := fun _ ↦ ℝ) a x) 0 u := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp
  · simp

/-- A one-dimensional variance estimate on every coordinate slice gives
the corresponding sum of energies under the product Gaussian law. -/
theorem variance_standardGaussianProduct_le_sum_of_slices (n : ℕ)
    (F : (Fin n → ℝ) → ℝ) (D : Fin n → (Fin n → ℝ) → ℝ)
    (hF : MemLp F 2 (standardGaussianProduct n))
    (hD : ∀ i, Integrable (fun x ↦ D i x ^ 2) (standardGaussianProduct n))
    (hslice : ∀ (i : Fin n) (x : Fin n → ℝ),
      Var[(fun t ↦ F (Function.update x i t)); gaussianReal 0 1] ≤
        ∫ t, D i (Function.update x i t) ^ 2 ∂gaussianReal 0 1) :
    Var[F; standardGaussianProduct n] ≤
      ∑ i, ∫ x, D i x ^ 2 ∂standardGaussianProduct n := by
  induction n with
  | zero =>
    have he : F = fun _ ↦ F (fun i ↦ Fin.elim0 i) := by
      funext x
      exact congrArg F (Subsingleton.elim _ _)
    rw [he, variance_eq_integral aemeasurable_const]
    simp [integral_const, probReal_univ]
  | succ n ih =>
    let σ := gaussianReal 0 1
    let γ := standardGaussianProduct n
    have : IsProbabilityMeasure γ := inferInstanceAs (IsProbabilityMeasure (standardGaussianProduct n))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    have he : MeasurePreserving e (standardGaussianProduct (n + 1)) (σ.prod γ) :=
      measurePreserving_piFinSuccAbove (fun _ ↦ σ) 0
    have he' (t : ℝ) (x : Fin n → ℝ) : e.symm (t, x) = Fin.cons t x := by
      exact Fin.insertNth_zero' t x
    let F' (z : ℝ × (Fin n → ℝ)) := F (e.symm z)
    let W (i : Fin (n + 1)) (z : ℝ × (Fin n → ℝ)) := D i (e.symm z) ^ 2
    let G (s : ℝ) (x : Fin n → ℝ) := F (Fin.cons s x)
    let D' (s : ℝ) (i : Fin n) (x : Fin n → ℝ) := D i.succ (Fin.cons s x)
    have hF' : MemLp F' 2 (σ.prod γ) := hF.comp_measurePreserving (he.symm e)
    have hW (i : Fin (n + 1)) : Integrable (W i) (σ.prod γ) :=
      (he.symm e).integrable_comp_of_integrable (hD i)
    have hWint (i : Fin (n + 1)) :
        (∫ z, W i z ∂σ.prod γ) = ∫ x, D i x ^ 2 ∂standardGaussianProduct (n + 1) :=
      (he.symm e).integral_comp' (fun x ↦ D i x ^ 2)
    have hFvar : Var[F'; σ.prod γ] = Var[F; standardGaussianProduct (n + 1)] :=
      (he.symm e).variance_fun_comp hF.aemeasurable
    have hF'₂ : Integrable (fun z ↦ F' z ^ 2) (σ.prod γ) := hF'.integrable_sq
    have hF'i : Integrable F' (σ.prod γ) := hF'.integrable (by simp)
    have hWseq : ∀ᵐ s ∂σ, ∀ i : Fin n, Integrable (fun x ↦ W i.succ (s, x)) γ :=
      ae_all_iff.mpr (fun i ↦ (hW i.succ).prod_right_ae)
    have hpoint : ∀ᵐ s ∂σ, Var[(fun x ↦ F' (s, x)); γ] ≤
        ∑ i : Fin n, ∫ x, W i.succ (s, x) ∂γ := by
      filter_upwards [hF'i.prod_right_ae, hF'₂.prod_right_ae, hWseq] with s h₁ h₂ h₃
      have hmem : MemLp (G s) 2 γ := by
        have hh := (memLp_two_iff_integrable_sq h₁.aestronglyMeasurable).2 h₂
        simpa only [F', G, he'] using hh
      have hD' (i : Fin n) : Integrable (fun x ↦ D' s i x ^ 2) γ := by
        simpa only [D', W, he'] using h₃ i
      have hs (i : Fin n) (x : Fin n → ℝ) :
          Var[(fun t ↦ G s (Function.update x i t)); σ] ≤
            ∫ t, D' s i (Function.update x i t) ^ 2 ∂σ := by
        simpa only [G, D', cons_update_tail] using hslice i.succ (Fin.cons s x)
      simpa only [F', W, G, D', he'] using ih (G s) (D' s) hmem hD' hs
    have hhead (x : Fin n → ℝ) :
        Var[(fun s ↦ F' (s, x)); σ] ≤ ∫ s, W 0 (s, x) ∂σ := by
      simpa only [F', W, he', ← cons_update_head (0 : ℝ)] using hslice 0 (Fin.cons 0 x)
    have hbound_tail :=
      integral_mono_of_nonneg (μ := σ) (ae_of_all _ (fun _ ↦ variance_nonneg _ _))
        (integrable_finsetSum Finset.univ fun i _ ↦ (hW i.succ).integral_prod_left) hpoint
    have hbound_head :=
      integral_mono_of_nonneg (μ := γ) (ae_of_all _ (fun _ ↦ variance_nonneg _ _))
        (hW 0).integral_prod_right (ae_of_all _ hhead)
    rw [integral_finsetSum _ (fun i _ ↦ (hW i.succ).integral_prod_left)] at hbound_tail
    have hswap (i : Fin n) : (∫ s, ∫ x, W i.succ (s, x) ∂γ ∂σ) =
        ∫ z, W i.succ z ∂σ.prod γ := (integral_prod _ (hW i.succ)).symm
    simp_rw [hswap, hWint] at hbound_tail
    rw [← integral_prod_symm _ (hW 0), hWint] at hbound_head
    have h := (variance_prod_le_integral_slice_variances F' hF').trans (add_le_add hbound_tail hbound_head)
    rw [hFvar] at h
    rw [Fin.sum_univ_succ]
    exact h.trans_eq (add_comm _ _)

end BoundedEdgeRegularSubgraphs
