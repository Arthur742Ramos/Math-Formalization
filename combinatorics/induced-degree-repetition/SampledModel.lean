module

public import ColumnSpace
public import SmallGenerators
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Finset Submodule Matrix Approximation
open scoped Classical
variable {q : ℕ} [NeZero q] {X Y I J : Type*} [Fintype I]

@[expose] noncomputable def coefficients (A : X → Y → ZMod q) (xs : I → X) (ys : J → Y)
    (x : X) : I → ZMod q :=
  if h : ∃ c : I → ZMod q, ∀ j, ∑ i, c i * A (xs i) (ys j) = A x (ys j)
    then h.choose else 0

@[expose] noncomputable def model (A : X → Y → ZMod q) (xs : I → X) (ys : J → Y)
    (x : X) (y : Y) := ∑ i, coefficients A xs ys x i * A (xs i) y

theorem match_columns (A : X → Y → ZMod q) (xs : I → X) (ys : J → Y) (x : X)
    (h : ∃ c : I → ZMod q, ∀ j, ∑ i, c i * A (xs i) (ys j) = A x (ys j)) :
    ∀ j, model A xs ys x (ys j) = A x (ys j) := by
  unfold model coefficients
  rw [dite_eq_left h]
  exact h.choose_spec

theorem model_complexity (A : X → Y → ZMod q) (xs : I → X) (ys : J → Y)
    (S : Finset X) (U : Finset Y) :
    complexity (model A xs ys) S U ≤ Fintype.card I * Real.log q := by
  let c := coefficients A xs ys
  let f : (I → ZMod q) →ₗ[ZMod q] (S → ZMod q) :=
    {toFun := fun v x => c x ⬝ᵥ v
     map_add' := fun v w => funext fun x => dotProduct_add _ _ _
     map_smul' := fun t v => funext fun x => dotProduct_smul _ _ _}
  have incl : colSpace (model A xs ys) S U ≤ LinearMap.range f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y,_,rfl⟩
    exact ⟨(fun i => A (xs i) y),rfl⟩
  have size := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective incl)
  have sur : Function.Surjective f.rangeRestrict := by rintro ⟨_,a,rfl⟩; exact ⟨a,rfl⟩
  have hs := size.trans (Nat.card_le_card_of_surjective _ sur)
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,ZMod.card] at hs
  have h := Real.log_le_log (by exact_mod_cast Fintype.card_pos)
    (show (Fintype.card (colSpace (model A xs ys) S U) : ℝ) ≤ (q:ℝ)^Fintype.card I by exact_mod_cast hs)
  simpa [complexity,Nat.card_eq_fintype_card,Real.log_pow] using h

omit [NeZero q] in
theorem determined_by_columns (A : Matrix I J (ZMod q)) (C : Finset J)
    (gen : span (ZMod q) (A.col '' (C : Set J)) = span _ (Set.range A.col))
    (v w : J → ZMod q) (hv : v ∈ span (ZMod q) (Set.range A.row))
    (hw : w ∈ span (ZMod q) (Set.range A.row)) (agree : ∀ j ∈ C, v j = w j) : v = w := by
  have h := (span (ZMod q) (Set.range A.row)).sub_mem hv hw
  rw [← range_vecMulLinear] at h
  obtain ⟨a,h⟩ := h
  let p := (dotProductBilin (ZMod q) (ZMod q)) a
  have ker : span (ZMod q) (Set.range A.col) ≤ LinearMap.ker p := by
    rw [← gen]
    apply span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    have eq := congrFun h j
    change a ⬝ᵥ A.col j = v j - w j at eq
    simpa [LinearMap.mem_ker,p,agree j hj] using eq
  funext j
  have ze := ker (subset_span (Set.mem_range_self j))
  change a ⬝ᵥ A.col j = 0 at ze
  have eq := congrFun h j
  change a ⬝ᵥ A.col j = v j - w j at eq
  exact sub_eq_zero.mp (eq.symm.trans ze)

theorem sampled_model_exact (A : X → Y → ZMod q) (xs : I → X) (ys : J → Y)
    (R : Finset I) (C : Finset J) (M : Matrix I J (ZMod q))
    (mat : ∀ i j, M i j = A (xs i) (ys j))
    (rows : span (ZMod q) (M.row '' (R : Set I)) = span _ (Set.range M.row))
    (cols : span (ZMod q) (M.col '' (C : Set J)) = span _ (Set.range M.col)) :
    ∀ i j, model A (fun t : R => xs t) (fun t : C => ys t) (xs i) (ys j) = M i j := by
  classical
  intro i
  let xR := fun t : R => xs t
  let yC := fun t : C => ys t
  have row : M.row i ∈ span (ZMod q) (Set.range M.row) := subset_span (Set.mem_range_self i)
  obtain ⟨c,hc⟩ := (Fintype.mem_span_image_iff_exists_fun (ZMod q)).mp (rows ▸ row)
  have match' : ∀ j : C, ∑ t : R, c t * A (xR t) (yC j) = A (xs i) (yC j) := by
    intro j
    simpa [Finset.sum_apply,Matrix.row_apply,mat,xR,yC] using congrFun hc (j:J)
  let co := coefficients A xR yC (xs i)
  let v := ∑ t : R, co t • M.row t
  have hv : v ∈ span (ZMod q) (Set.range M.row) :=
    sum_mem fun t _ => smul_mem _ _ (subset_span (Set.mem_range_self (t:I)))
  have eval (j : J) : v j = model A xR yC (xs i) (ys j) := by
    simp [v,co,model,Finset.sum_apply,Matrix.row_apply,mat,xR,yC]
  have agree (j : J) (hj : j ∈ C) : v j = M.row i j := by
    rw [eval,Matrix.row_apply,mat]
    exact match_columns A xR yC (xs i) ⟨c,match'⟩ ⟨j,hj⟩
  have eq := determined_by_columns M C cols _ _ hv row agree
  exact fun j => (eval j).symm.trans (congrFun eq j)

end InducedDegreeRepetition.Restriction
