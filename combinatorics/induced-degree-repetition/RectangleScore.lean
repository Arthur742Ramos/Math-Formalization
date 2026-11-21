module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Approximation

open Finset
open scoped Classical
variable {X Y : Type*}

@[expose] def total (w : X → Y → ℝ) (S : Finset X) (U : Finset Y) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ U, w x y

theorem total_sub_rows (w : X → Y → ℝ) (S S' : Finset X) (U : Finset Y) (h : S' ⊆ S) :
    total w (S \ S') U = total w S U - total w S' U := by
  unfold total
  exact eq_sub_of_add_eq (sum_sdiff h)

theorem total_sub_cols (w : X → Y → ℝ) (S : Finset X) (U U' : Finset Y) (h : U' ⊆ U) :
    total w S (U \ U') = total w S U - total w S U' := by
  unfold total
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun x _ => eq_sub_of_add_eq (sum_sdiff h)

/-- Select a maximum-score subrectangle. Deleting rows or columns with negative
score would improve it. Every full strip therefore has nonnegative score. -/
theorem score_core (w : X → Y → ℝ) (X₀ : Finset X) (Y₀ : Finset Y) :
    ∃ S ⊆ X₀, ∃ U ⊆ Y₀, total w X₀ Y₀ ≤ total w S U ∧
      (∀ R ⊆ S, 0 ≤ total w R U) ∧ (∀ V ⊆ U, 0 ≤ total w S V) := by
  classical
  let choices := X₀.powerset ×ˢ Y₀.powerset
  have root : (X₀,Y₀) ∈ choices := by simp [choices]
  obtain ⟨⟨S,U⟩,mem,h⟩ := exists_max_image choices (fun p => total w p.1 p.2) ⟨_,root⟩
  have sub := mem_product.mp mem
  have sx := mem_powerset.mp sub.1
  have uy := mem_powerset.mp sub.2
  refine ⟨S,sx,U,uy,h _ root,?_,?_⟩
  · intro R hr
    have mem : (S \ R,U) ∈ choices := mem_product.mpr ⟨mem_powerset.mpr (sdiff_subset.trans sx),sub.2⟩
    have bound := h _ mem
    change total w (S \ R) U ≤ total w S U at bound
    rw [total_sub_rows w S R U hr] at bound
    linarith
  · intro V hv
    have mem : (S,U \ V) ∈ choices := mem_product.mpr ⟨sub.1,mem_powerset.mpr (sdiff_subset.trans uy)⟩
    have bound := h _ mem
    change total w S (U \ V) ≤ total w S U at bound
    rw [total_sub_cols w S U V hv] at bound
    linarith

@[expose] noncomputable def errors (bad : X → Y → Prop) (S : Finset X) (U : Finset Y) : ℝ :=
  total (fun x y => if bad x y then 1 else 0) S U

theorem errors_nonneg (bad : X → Y → Prop) (S : Finset X) (U : Finset Y) : 0 ≤ errors bad S U :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by dsimp; split <;> norm_num

theorem total_score (bad : X → Y → Prop) (d : ℝ) (S : Finset X) (U : Finset Y) :
    total (fun x y => d - (if bad x y then 1 else 0)) S U =
      d*S.card*U.card - errors bad S U := by
  simp only [total,errors,sum_sub_distrib,sum_const,nsmul_eq_mul]
  ring

/-- A low-error rectangle has a large subrectangle on which *every* row strip and
every column strip has error density at most d+η. -/
theorem refine_errors (bad : X → Y → Prop) (X₀ : Finset X) (Y₀ : Finset Y)
    (hx : 0 < X₀.card) (hy : 0 < Y₀.card) (d η : ℝ) (hd : 0 ≤ d) (he : 0 < η)
    (low : errors bad X₀ Y₀ ≤ d*X₀.card*Y₀.card) :
    ∃ S ⊆ X₀, ∃ U ⊆ Y₀, η/(d+η)*X₀.card ≤ S.card ∧ η/(d+η)*Y₀.card ≤ U.card ∧
      (∀ R ⊆ S, errors bad R U ≤ (d+η)*R.card*U.card) ∧
      (∀ V ⊆ U, errors bad S V ≤ (d+η)*S.card*V.card) := by
  obtain ⟨S,hs,U,hu,score,rows,cols⟩ := score_core (fun x y => d+η-(if bad x y then 1 else 0)) X₀ Y₀
  simp_rw [total_score] at score rows cols
  have ep : 0 < d+η := by linarith
  have xy : η*X₀.card*Y₀.card ≤ (d+η)*S.card*U.card := by linarith [errors_nonneg bad S U]
  have xs : (S.card:ℝ) ≤ X₀.card := by exact_mod_cast card_le_card hs
  have yu : (U.card:ℝ) ≤ Y₀.card := by exact_mod_cast card_le_card hu
  refine ⟨S,hs,U,hu,?_,?_,fun R hr => sub_nonneg.mp (rows R hr),fun V hv => sub_nonneg.mp (cols V hv)⟩
  · rw [div_mul_eq_mul_div,div_le_iff₀ ep]
    have h := xy.trans (mul_le_mul_of_nonneg_left yu (by positivity))
    exact le_of_mul_le_mul_right (by nlinarith only [h]) (by exact_mod_cast hy : (0:ℝ)<Y₀.card)
  · rw [div_mul_eq_mul_div,div_le_iff₀ ep]
    have h := xy.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left xs ep.le) (Nat.cast_nonneg _))
    exact le_of_mul_le_mul_right (by nlinarith only [h]) (by exact_mod_cast hx : (0:ℝ)<X₀.card)

end InducedDegreeRepetition.Approximation
