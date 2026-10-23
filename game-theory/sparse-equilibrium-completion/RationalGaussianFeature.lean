/- AI-assisted formalization; Apache-2.0, following the parent repository.
Strict module compilation evidence is retained in attempts/.
This bridge reuses the already compiled direction,
deletion, and dimension theorems by importing their existing module. FM remains
in the import closure but is not called by the runtime definitions below.
-/
module
public import RationalGaussianKernel
public import RationalFeatureDimension
public import Mathlib.Data.Fin.Tuple.Basic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Homogeneous feature, mass, and inactive-coordinate equations. In contrast
to the FM search, no coordinate-normalization equation or repeated LP is needed.
Rows are explicitly enumerated as Fin (d+(m+1)); no Fintype.equivFin is used. -/
def gaussianFeatureRows {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) : Fin (d+(m+1)) → Fin m → ℚ :=
  Fin.addCases A (Fin.cons (fun _ => 1)
    (fun i j => if 0 < q i then 0 else if j = i then 1 else 0))

theorem gaussian_feature_equations_iff {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ) :
    Gaussian.IsKernel (Gaussian.tableOfFn (gaussianFeatureRows A q)) w ↔
      RationalFeatureDirection A q w := by
  constructor
  · intro h
    have ha : ∀ a, ∑ i, A a i * w i = 0 := by
      intro a
      simpa [Gaussian.IsKernel, Gaussian.dot, gaussianFeatureRows]
        using h (Fin.castAdd (m+1) a)
    have hm : ∑ i, w i = 0 := by
      simpa [Gaussian.IsKernel, Gaussian.dot, gaussianFeatureRows]
        using h (Fin.natAdd d 0)
    refine ⟨ha, hm, ?_⟩
    intro i hi
    by_contra hn
    have hz := h (Fin.natAdd d i.succ)
    have hw : w i = 0 := by
      simpa [Gaussian.dot, gaussianFeatureRows, hn] using hz
    exact hi hw
  · rintro ⟨ha, hm, hs⟩ row
    refine Fin.addCases ?_ ?_ row
    · intro a
      simpa [Gaussian.dot, gaussianFeatureRows] using ha a
    · intro row
      refine Fin.cases ?_ ?_ row
      · simpa [Gaussian.dot, gaussianFeatureRows] using hm
      · intro i
        by_cases hi : 0 < q i
        · simp [Gaussian.dot, gaussianFeatureRows, hi]
        · have hw : w i = 0 := by
            by_contra hn
            exact hi (hs i hn)
          simpa [Gaussian.dot, gaussianFeatureRows, hi] using hw

/-- Actual rational feature kernel discovery, with deterministic Gaussian
elimination over explicit tables. The final function closes over a computed
Vector, so repeated coordinate reads do not recompute back-substitution. -/
def rationalGaussianFeatureKernel {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) : Option (Fin m → ℚ) :=
  (Gaussian.kernel (d+(m+1)) m
    (Gaussian.tableOfFn (gaussianFeatureRows A q))).map List.Vector.get

theorem rational_gaussian_feature_sound {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ)
    (h : rationalGaussianFeatureKernel A q = some w) :
    RationalFeatureDirection A q w ∧ ∃ i, w i ≠ 0 := by
  cases he : Gaussian.kernel (d+(m+1)) m
      (Gaussian.tableOfFn (gaussianFeatureRows A q)) with
  | none => simp [rationalGaussianFeatureKernel, he] at h
  | some v =>
    have hv : v.get = w := by simpa [rationalGaussianFeatureKernel, he] using h
    obtain ⟨hd, hn⟩ := Gaussian.kernel_sound _ _ _ v he
    rw [← hv]
    exact ⟨(gaussian_feature_equations_iff A q v.get).mp hd, hn⟩

theorem rational_gaussian_feature_complete {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ)
    (hw : RationalFeatureDirection A q w) (hn : ∃ i, w i ≠ 0) :
    ∃ v, rationalGaussianFeatureKernel A q = some v := by
  obtain ⟨v, hv⟩ := Gaussian.kernel_complete (d+(m+1)) m
    (Gaussian.tableOfFn (gaussianFeatureRows A q)) w
    ((gaussian_feature_equations_iff A q w).mpr hw) hn
  exact ⟨v.get, by simp [rationalGaussianFeatureKernel, hv]⟩

def rationalGaussianFeatureDelete {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) : Option (Fin m → ℚ) :=
  (rationalGaussianFeatureKernel A q).map (rationalFeatureDelete q)

theorem rational_gaussian_deletion_above_dimension {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1)
    (hcard : d < (rationalWeightSupport q).card) :
    ∃ v, rationalGaussianFeatureDelete A q = some v ∧
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, q i ∧
      (∀ a, (∑ i, v i * A a i) = ∑ i, q i * A a i) ∧
      (∀ i, q i = 0 → v i = 0) ∧
      (rationalWeightSupport v).card < (rationalWeightSupport q).card := by
  obtain ⟨w, hw, hn⟩ := rational_feature_direction_of_card A q hq a₀ hmass hcard
  obtain ⟨w, hw⟩ := rational_gaussian_feature_complete A q w hw hn
  obtain ⟨⟨ha, hm, hs⟩, hn⟩ := rational_gaussian_feature_sound A q w hw
  refine ⟨rationalFeatureDelete q w, ?_, ?_⟩
  · simp [rationalGaussianFeatureDelete, hw]
  · exact rational_feature_delete_contract A q w hq hm
      (fun a => by simpa only [mul_comm] using ha a) hs hn

end SparseCompletion
