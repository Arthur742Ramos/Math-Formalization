module

public import BoundedEdgeRegularSubgraphs.GaussianProductParts
import Mathlib.Tactic

/-!
# A Gaussian integration-by-parts identity for a composed test function
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The integration-by-parts identity used in Lemma A.2. The negative
Ornstein–Uhlenbeck generator is written using the first and diagonal second
partial derivatives of the auxiliary function. -/
theorem gaussianProduct_stein_identity {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℝ)
    (dF dG ddG : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (b b' : ℝ → ℝ) (hb : ∀ t, HasDerivAt b (b' t) t)
    (hF : ∀ i (y : Fin n → ℝ) t, HasDerivAt (fun s ↦ F (i.insertNth s y))
      (dF i (i.insertNth t y)) t)
    (hG : ∀ i (y : Fin n → ℝ) t, HasDerivAt (fun s ↦ dG i (i.insertNth s y))
      (ddG i (i.insertNth t y)) t)
    (hK : ∀ i, Integrable (fun x ↦ b (F x) * dG i x) (standardGaussianProduct (n + 1)))
    (hX : ∀ i, Integrable (fun x ↦ x i * (b (F x) * dG i x)) (standardGaussianProduct (n + 1)))
    (hY : ∀ i, Integrable (fun x ↦ b (F x) * ddG i x) (standardGaussianProduct (n + 1)))
    (hZ : ∀ i, Integrable (fun x ↦ b' (F x) * dF i x * dG i x) (standardGaussianProduct (n + 1))) :
    (∫ x, b (F x) * (∑ i, (x i * dG i x - ddG i x)) ∂standardGaussianProduct (n + 1)) =
      ∫ x, b' (F x) * (∑ i, dF i x * dG i x) ∂standardGaussianProduct (n + 1) := by
  let γ := standardGaussianProduct (n + 1)
  let X (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) := x i * (b (F x) * dG i x)
  let Y (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) := b (F x) * ddG i x
  let Z (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) := b' (F x) * dF i x * dG i x
  have hd (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s ↦ b (F (i.insertNth s y)) * dG i (i.insertNth s y))
        (Z i (i.insertNth t y) + Y i (i.insertNth t y)) t := by
    have h := (hb (F (i.insertNth t y))).comp t (hF i y t)
    have h' : HasDerivAt (fun s ↦ b (F (i.insertNth s y)))
        (b' (F (i.insertNth t y)) * dF i (i.insertNth t y)) t := h
    exact h'.fun_mul (hG i y t)
  have hparts (i : Fin (n + 1)) :
      (∫ x, X i x - Y i x ∂γ) = ∫ x, Z i x ∂γ := by
    have h := integral_standardGaussianProduct_partial i (fun x ↦ b (F x) * dG i x)
      (fun x ↦ Z i x + Y i x) (hd i) (hK i) ((hZ i).add (hY i)) (hX i)
    change (∫ x, Z i x + Y i x ∂γ) = ∫ x, X i x ∂γ at h
    have hzi : Integrable (Z i) γ := hZ i
    have hyi : Integrable (Y i) γ := hY i
    have hxi : Integrable (X i) γ := hX i
    rw [integral_add hzi hyi] at h
    rw [integral_sub hxi hyi]
    linarith only [h]
  have hleft (x : Fin (n + 1) → ℝ) :
      b (F x) * (∑ i, (x i * dG i x - ddG i x)) = ∑ i, (X i x - Y i x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ by dsimp only [X, Y]; ring)
  have hright (x : Fin (n + 1) → ℝ) :
      b' (F x) * (∑ i, dF i x * dG i x) = ∑ i, Z i x := by
    simp only [Z, Finset.mul_sum, mul_assoc]
  simp_rw [hleft, hright]
  have hsum (i : Fin (n + 1)) (_ : i ∈ Finset.univ) :
      Integrable (fun x ↦ X i x - Y i x) γ := (hX i).sub (hY i)
  rw [integral_finsetSum _ hsum, integral_finsetSum _ (fun i _ ↦ hZ i)]
  exact Finset.sum_congr rfl (fun i _ ↦ hparts i)

/-- The cubic polynomial of one Gaussian linear form is the negative
generator of the cubic-plus-linear auxiliary polynomial in Lemma A.2. -/
theorem gaussian_cubic_generator {ι : Type*} [Fintype ι]
    (v x : ι → ℝ) :
    let y := ∑ i, v i * x i
    let c := ∑ i, v i ^ 2
    (∑ i, (x i * ((y ^ 2 + 2 * c) * v i) - 2 * y * v i ^ 2)) = y ^ 3 := by
  intro y c
  have hleft (i : ι) : x i * ((y ^ 2 + 2 * c) * v i) =
      (y ^ 2 + 2 * c) * (v i * x i) := by ring
  simp only [Finset.sum_sub_distrib, hleft, ← Finset.mul_sum]
  change (y ^ 2 + 2 * c) * y - 2 * y * c = y ^ 3
  ring

end BoundedEdgeRegularSubgraphs
