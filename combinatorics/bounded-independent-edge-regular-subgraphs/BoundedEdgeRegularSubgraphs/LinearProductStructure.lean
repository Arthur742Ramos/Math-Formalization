module

public import BoundedEdgeRegularSubgraphs.LinearProductUpper
public import BoundedEdgeRegularSubgraphs.Theorem11
import Mathlib.Tactic

/-!
# The rank and Lipschitz structure of the linear product example
-/

@[expose] public section

namespace BoundedEdgeRegularSubgraphs

abbrev UnitCubeLine := Fin 1 → Set.Icc (0 : ℝ) 1

theorem linearWeight_mem {a b : ℝ} (hb : 0 ≤ b) (x : UnitCubeLine) :
    a + b * (x 0 : ℝ) ∈ Set.Icc a (a + b) :=
  ⟨le_add_of_nonneg_right (mul_nonneg hb (x 0).property.1),
    by linarith only [mul_le_of_le_one_right hb (x 0).property.2]⟩

/-- The symmetric kernel generating the linear product array. -/
noncomputable def linearProductKernel (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : a + b ≤ 1) (x y : UnitCubeLine) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨(a + b * (x 0 : ℝ)) * (a + b * (y 0 : ℝ)),
    mul_nonneg (ha.trans (linearWeight_mem hb x).1) (ha.trans (linearWeight_mem hb y).1),
    (mul_le_of_le_one_right (ha.trans (linearWeight_mem hb x).1)
      ((linearWeight_mem hb y).2.trans ht)).trans ((linearWeight_mem hb x).2.trans ht)⟩

/-- The kernel is Lipschitz in one variable with constant at most `b`. -/
theorem linearProductKernel_lipschitz (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : a + b ≤ 1) :
    CubeLipschitz b (linearProductKernel a b ha hb ht) := by
  intro x y z ε _ hxy
  let c := a + b * (z 0 : ℝ)
  have hc : 0 ≤ c := ha.trans (linearWeight_mem (a := a) hb z).1
  have hct : c ≤ 1 := (linearWeight_mem (a := a) hb z).2.trans ht
  change |(a + b * (x 0 : ℝ)) * c - (a + b * (y 0 : ℝ)) * c| ≤ b * ε
  rw [show (a + b * (x 0 : ℝ)) * c - (a + b * (y 0 : ℝ)) * c =
    b * ((x 0 : ℝ) - y 0) * c by ring, abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
  exact (mul_le_of_le_one_right (mul_nonneg hb (abs_nonneg _)) hct).trans
    (mul_le_mul_of_nonneg_left (hxy 0) hb)

private theorem linearProductKernel_floor {ξ a b : ℝ} (hξ : 0 ≤ ξ)
    (hξ' : ξ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : a + b ≤ 1)
    (hlo : Real.sqrt ξ ≤ a) (hhi : a + b ≤ Real.sqrt (1 - ξ))
    (x y : UnitCubeLine) :
    ξ ≤ (linearProductKernel a b ha hb ht x y : ℝ) ∧
      (linearProductKernel a b ha hb ht x y : ℝ) ≤ 1 - ξ := by
  let x' := a + b * (x 0 : ℝ)
  let y' := a + b * (y 0 : ℝ)
  have hx := linearWeight_mem (a := a) hb x
  have hy := linearWeight_mem (a := a) hb y
  change ξ ≤ x' * y' ∧ x' * y' ≤ 1 - ξ
  constructor
  · have h := mul_le_mul (hlo.trans hx.1) (hlo.trans hy.1) (Real.sqrt_nonneg ξ) (ha.trans hx.1)
    rwa [← pow_two, Real.sq_sqrt hξ] at h
  · have h := mul_le_mul (hx.2.trans hhi) (hy.2.trans hhi) (ha.trans hy.1)
      (Real.sqrt_nonneg _)
    rwa [← pow_two, Real.sq_sqrt (sub_nonneg.mpr hξ')] at h

/-- For every interior floor, the same linear product model has a rank-one
completion and a one-dimensional Lipschitz representation. The vertex
weight interval is chosen by taking square roots of the edge bounds. -/
theorem exists_linear_product_structure (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b < 1 ∧
      ∃ W : UnitCubeLine → UnitCubeLine → Set.Icc (0 : ℝ) 1,
        (∀ x y, W x y = W y x) ∧ CubeLipschitz b W ∧
        (∀ x y, ξ ≤ (W x y : ℝ) ∧ (W x y : ℝ) ≤ 1 - ξ) ∧
        ∀ n : ℕ, ∃ p : Edge (Fin n) → Set.Icc (0 : ℝ) 1, HasFloor ξ p ∧
          HasRankCompletion 1 p ∧
          (∀ e, (p e : ℝ) = linearVertexWeight a b e.val.1 * linearVertexWeight a b e.val.2) ∧
          ∃ x : Fin n → UnitCubeLine, ∀ e, p e = W (x e.val.1) (x e.val.2) := by
  let s := Real.sqrt ξ
  let t := Real.sqrt (1 - ξ)
  have hs : 0 < s := Real.sqrt_pos.2 hξ
  have hst : s < t := Real.sqrt_lt_sqrt hξ.le (by linarith)
  have ht : t < 1 := by
    calc
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      _ = _ := Real.sqrt_one
  let a := (2 * s + t) / 3
  let b := (t - s) / 3
  have ha : 0 < a := by dsimp only [a]; linarith
  have hb : 0 < b := by dsimp only [b]; linarith
  have hab : a + b < t := by dsimp only [a, b]; linarith
  have hat : a + b < 1 := hab.trans ht
  have hsa : s ≤ a := by dsimp only [a]; linarith
  let W := linearProductKernel a b ha.le hb.le hat.le
  have hW (x y : UnitCubeLine) : ξ ≤ (W x y : ℝ) ∧ (W x y : ℝ) ≤ 1 - ξ :=
    linearProductKernel_floor hξ.le (by linarith) ha.le hb.le hat.le hsa hab.le x y
  refine ⟨a, b, ha, hb, hat, W, ?_, linearProductKernel_lipschitz a b ha.le hb.le hat.le, hW, ?_⟩
  · intro x y
    exact Subtype.ext (mul_comm _ _)
  · intro n
    let x (i : Fin n) (_ : Fin 1) : Set.Icc (0 : ℝ) 1 :=
      ⟨((i.val : ℝ) + 1) / n, by
        constructor
        · positivity
        · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr i.isLt.pos
          apply (div_le_one hn).2
          exact_mod_cast Nat.succ_le_of_lt i.isLt⟩
    let p (e : Edge (Fin n)) := W (x e.val.1) (x e.val.2)
    have hw (i j : Fin n) : (W (x i) (x j) : ℝ) =
        linearVertexWeight a b i * linearVertexWeight a b j := by
      dsimp only [W, linearProductKernel, x, linearVertexWeight]
      simp only [mul_div_assoc]
    refine ⟨p, fun e ↦ hW _ _, ?_, fun e ↦ hw _ _, x, fun _ ↦ rfl⟩
    let w := linearVertexWeight a b (n := n)
    refine ⟨Matrix.vecMulVec w w, fun _ _ ↦ mul_comm _ _, ?_,
      Matrix.rank_vecMulVec_le w w, fun e ↦ (hw e.val.1 e.val.2).symm⟩
    intro i j
    change w i * w j ∈ Set.Icc 0 1
    rw [← hw i j]
    exact (W (x i) (x j)).property

end BoundedEdgeRegularSubgraphs
