/- AI-assisted formalization under repository Apache-2.0.
Select independent ORIGINAL active rows after earning their
trivial common kernel. Classical basis selection is proof-only. -/
module
public import RationalLPActiveRows
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Finite
@[expose] public section
open scoped BigOperators Matrix
namespace SparseCompletion

theorem rational_lp_select_nonsingular_rows {I : Type*} [Fintype I] {n : ℕ}
    (A : I → Fin n → ℝ)
    (hker : ∀ v : Fin n → ℝ, (∀ i, ∑ j, A i j*v j = 0) → v = 0) :
    ∃ e : Fin n → I, Function.Injective e ∧ Matrix.det (fun i j => A (e i) j : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ A
  let _ : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  let B : Matrix κ (Fin n) ℝ := fun i j => A (a i) j
  have hBker (v : Fin n → ℝ) (hv : B *ᵥ v = 0) : v = 0 := by
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun w => ∑ j, w j*v j
        map_add' := by intro w z; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro c w
          simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply] }
    have hle : Submodule.span ℝ (Set.range (A ∘ a)) ≤ LinearMap.ker L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact congrFun hv i
    apply hker v
    intro i
    have hm : A i ∈ Submodule.span ℝ (Set.range A) := Submodule.subset_span ⟨i,rfl⟩
    rw [← hspan] at hm
    exact hle hm
  have hBinj : Function.Injective B.mulVecLin := by
    intro v w he
    apply sub_eq_zero.mp
    apply hBker
    change B *ᵥ v = B *ᵥ w at he
    rw [Matrix.mulVec_sub, he, sub_self]
  have hlow : n ≤ Fintype.card κ := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      (LinearMap.finrank_le_finrank_of_injective hBinj)
  have hupp : Fintype.card κ ≤ n := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hli.fintype_card_le_finrank
  let f : Fin n ≃ κ := (Fintype.equivFinOfCardEq (le_antisymm hupp hlow)).symm
  refine ⟨a ∘ f,ha.comp f.injective,?_⟩
  have hli' : LinearIndependent ℝ (fun i : Fin n => A (a (f i))) := hli.comp f f.injective
  apply IsUnit.ne_zero
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli')

/-- The selected rows are an injective subfamily of the literal finite row
type and are tight at an earned feasible point. No basis premise occurs. -/
theorem rational_lp_exists_active_basis {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (U : Fin n → ℝ)
    (hb : ∀ y, S.RealSatisfies y → ∀ j, |y j| ≤ U j)
    (hf : ∃ x, S.RealSatisfies x) :
    ∃ (x : Fin n → ℝ) (e : Fin n → I), S.RealSatisfies x ∧ Function.Injective e ∧
      (∀ i, rationalLPRealResponse S x (e i) = (S.rightSide (e i) : ℝ)) ∧
      Matrix.det (fun i j => S.coefficient (e i) j : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
  classical
  obtain ⟨x,hx,hker⟩ := rational_lp_exists_trivial_active_kernel S U hb hf
  let J := {row : I // rationalLPRealResponse S x row = (S.rightSide row : ℝ)}
  let _ : Fintype J := Fintype.ofFinite J
  let A : J → Fin n → ℝ := fun row j => (S.coefficient row.val j : ℝ)
  have hA : ∀ v : Fin n → ℝ, (∀ row, ∑ j, A row j*v j = 0) → v = 0 := by
    intro v hv
    apply hker v
    intro row hr
    exact hv (⟨row,hr⟩ : J)
  obtain ⟨e,he,hdet⟩ := rational_lp_select_nonsingular_rows A hA
  refine ⟨x,Subtype.val ∘ e,hx,Subtype.val_injective.comp he,fun i => (e i).property,?_⟩
  have hc : ((Matrix.det (fun i j => S.coefficient (e i).val j : Matrix (Fin n) (Fin n) ℚ) : ℚ) : ℝ) =
      Matrix.det (fun i j => A (e i) j : Matrix (Fin n) (Fin n) ℝ) := Rat.cast_det _
  intro hz
  apply hdet
  rw [← hc]
  simpa only [Function.comp_apply, Rat.cast_zero] using congrArg (fun q : ℚ => (q : ℝ)) hz

end SparseCompletion
