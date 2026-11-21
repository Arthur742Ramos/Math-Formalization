module

public import ColumnSpace
public import RectangleScore
public import DualityRectangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Approximation

open Finset
open scoped Classical
variable {X Y : Type*} {q : ℕ} [NeZero q]

theorem largest_class {I Z : Type*} [Fintype Z] [Nonempty Z] (U : Finset I) (c : I → Z) :
    ∃ z, (U.card:ℝ) ≤ Fintype.card Z * ((U.filter (fun y => c y = z)).card : ℝ) := by
  classical
  let f := fun z => ((U.filter (fun y => c y = z)).card : ℝ)
  obtain ⟨z,_,hz⟩ := exists_max_image (univ : Finset Z) f univ_nonempty
  refine ⟨z,?_⟩
  have h := sum_le_sum (s := (univ : Finset Z)) fun i _ => hz i (mem_univ i)
  have e := sum_fiberwise U c (fun _ => (1:ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at e
  simpa only [f,e,sum_const,card_univ,nsmul_eq_mul] using h

theorem errors_mono_rows (bad : X → Y → Prop) {S R : Finset X} (h : R ⊆ S) (U : Finset Y) :
    errors bad R U ≤ errors bad S U := by
  apply sum_le_sum_of_subset_of_nonneg h
  intro x _ _
  apply sum_nonneg
  intro y _
  dsimp
  split <;> norm_num

/-- At bounded image size a largest class of identical columns followed by a
residue class of rows gives a constant rectangle. The score core controls its error. -/
theorem terminal_rectangle (A : X → Y → ZMod q) (bad : X → Y → Prop)
    (S : Finset X) (U : Finset Y) (hs : S.Nonempty) (hu : U.Nonempty)
    (d : ℝ) (hd : 0 < d) (low : errors bad S U ≤ d*S.card*U.card) :
    ∃ R ⊆ S, ∃ V ⊆ U, ∃ t : ZMod q,
      (S.card:ℝ) ≤ 2*q*R.card ∧ (U.card:ℝ) ≤ 2*Real.exp (complexity A S U)*V.card ∧
      (∀ x ∈ R, ∀ y ∈ V, A x y = t) ∧ errors bad R V ≤ 2*d*q*R.card*V.card := by
  classical
  obtain ⟨R₀,rs,V₀,vu,hr,hv,_,cols⟩ := refine_errors bad S U (card_pos.mpr hs) (card_pos.mpr hu) d d hd.le hd low
  have half : d/(d+d) = 1/2 := by field_simp; ring
  rw [half] at hr hv
  let I := colSpace A S U
  let c (y : Y) : I := if hy : y ∈ U then ⟨column A S y,col_mem A S hy⟩ else 0
  obtain ⟨z,hz⟩ := largest_class V₀ c
  let V := V₀.filter (fun y => c y = z)
  let a (x : X) := if hx : x ∈ S then z.val ⟨x,hx⟩ else 0
  obtain ⟨t,ht⟩ := Duality.largest_residue_card R₀ a
  let R := R₀.filter fun x => a x = t
  have rr : R ⊆ R₀ := filter_subset _ _
  have vv : V ⊆ V₀ := filter_subset _ _
  have qp : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have rsize : (R₀.card:ℝ) ≤ q*R.card := by simpa [mul_comm] using (div_le_iff₀ qp).mp ht
  have csize : Real.exp (complexity A S U) = (Fintype.card I : ℝ) := by
    rw [complexity,Real.exp_log (by exact_mod_cast Nat.card_pos),Nat.card_eq_fintype_card]
  refine ⟨R,rr.trans rs,V,vv.trans vu,t,by linarith,?_,?_,?_⟩
  · rw [csize]
    have hz' : (V₀.card:ℝ) ≤ (Fintype.card I : ℝ)*(V.card:ℝ) := by
      convert hz using 2
      apply congrArg Nat.cast
      apply congrArg Finset.card
      ext i
      simp [V]
    linarith
  · intro x hx y hy
    have xx := rs (rr hx)
    have yy := vu (vv hy)
    have eq := congrArg (fun v : I => v.val ⟨x,xx⟩) (mem_filter.mp hy).2
    have az := (mem_filter.mp hx).2
    simp [c,yy,column] at eq
    simpa [a,xx,← eq] using az
  · have h := (errors_mono_rows bad rr V).trans (cols V vv)
    have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left rsize (by linarith : 0≤d+d)) (Nat.cast_nonneg V.card : 0 ≤ (V.card:ℝ))
    nlinarith only [h,h']

end InducedDegreeRepetition.Approximation
