module

public import BoundedEdgeRegularSubgraphs.CubeCells
public import BoundedEdgeRegularSubgraphs.DensitySurplus
import Mathlib.Tactic

/-!
# Near-balance from a bound on the range of the edge probabilities
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A common interval containing the edge probabilities contains both
the average density and every normalised expected degree. -/
theorem row_density_mem_Icc (q : Edge α → Icc (0 : ℝ) 1) (hn : 2 ≤ Fintype.card α)
    {a b : ℝ} (ha : ∀ e, a ≤ (q e : ℝ)) (hb : ∀ e, (q e : ℝ) ≤ b) :
    arrayDensity q ∈ Icc a b ∧ ∀ i, degreeSum (fun e ↦ (q e : ℝ)) i /
      ((Fintype.card α : ℝ) - 1) ∈ Icc a b := by
  have hn' : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hden : 0 < (Fintype.card α : ℝ) - 1 := by linarith only [hn']
  have hn₀ : (0 : ℝ) < Fintype.card α := by linarith only [hn']
  have hD : (∑ e : Edge α, (q e : ℝ)) / Fintype.card (Edge α) = arrayDensity q := by
    unfold arrayDensity
    rw [← card_edge_twice, mul_comm (2 : ℝ) (Fintype.card (Edge α) : ℝ),
      mul_comm (2 : ℝ) (∑ e : Edge α, (q e : ℝ)), mul_div_mul_right _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hDpos : (0 : ℝ) < Fintype.card (Edge α) := by
    have h := mul_pos hn₀ hden
    rw [← card_edge_twice] at h
    linarith only [h]
  constructor
  · rw [← hD]
    constructor
    · apply (le_div_iff₀ hDpos).2
      have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ ↦ ha e)
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm a] using h
    · apply (div_le_iff₀ hDpos).2
      have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ ↦ hb e)
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm b] using h
  · intro i
    have hsum (c : ℝ) : degreeSum (fun _ : Edge α ↦ c) i = c * ((Fintype.card α : ℝ) - 1) := by
      rw [← degreeSum_one i]
      unfold degreeSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ ↦ by split_ifs <;> simp)
    have hmono {f g : Edge α → ℝ} (h : ∀ e, f e ≤ g e) : degreeSum f i ≤ degreeSum g i := by
      unfold degreeSum
      exact Finset.sum_le_sum (fun e _ ↦ by split_ifs <;> simp [h])
    exact ⟨(le_div_iff₀ hden).2 ((hsum a).symm.le.trans (hmono ha)),
      (div_le_iff₀ hden).2 ((hmono hb).trans_eq (hsum b))⟩

/-- The finite large-cell hypothesis (6.1) for a Lipschitz kernel,
including the discrepancy around the induced array density. -/
theorem exists_lipschitz_nearBalanced_cell {d : ℕ}
    (S : Finset α) (x : α → (Fin d → Icc (0 : ℝ) 1))
    (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1)
    {h L : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hsym : ∀ a b, W a b = W b a) (hW : CubeLipschitz L W)
    (hsize : 2 ≤ (h / 2) ^ d * (S.card : ℝ)) :
    ∃ T ⊆ S, (h / 2) ^ d * (S.card : ℝ) ≤ T.card ∧
      let q (e : Edge ↥T) := W (x e.val.1.val) (x e.val.2.val)
      ∀ i : T, |degreeSum (fun e ↦ (q e : ℝ)) i / (T.card - 1 : ℝ) - arrayDensity q| ≤ 2 * L * h := by
  obtain ⟨T, hTS, hT, hdiam⟩ := exists_large_lipschitz_kernel_cell S x W hh hh₁ hsym hW
  refine ⟨T, hTS, hT, ?_⟩
  let q (e : Edge ↥T) := W (x e.val.1.val) (x e.val.2.val)
  have hT₂ : 2 ≤ Fintype.card T := by
    rw [Fintype.card_coe]
    exact_mod_cast hsize.trans hT
  have hT₀ : (0 : ℝ) < Fintype.card T := by exact_mod_cast (show 0 < Fintype.card T by omega)
  have hd₀ : (0 : ℝ) < (Fintype.card T : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT₂
    linarith only [h]
  have hE : (Finset.univ : Finset (Edge T)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    have h := mul_pos hT₀ hd₀
    rw [← card_edge_twice] at h
    exact_mod_cast (show (0 : ℝ) < Fintype.card (Edge T) by linarith only [h])
  obtain ⟨e₀, _, he₀⟩ := Finset.exists_min_image Finset.univ (fun e ↦ (q e : ℝ)) hE
  have ha (e : Edge T) : (q e₀ : ℝ) ≤ q e := he₀ e (Finset.mem_univ e)
  have hb (e : Edge T) : (q e : ℝ) ≤ (q e₀ : ℝ) + 2 * L * h := by
    have he := hdiam e.val.1.val e.val.1.property e.val.2.val e.val.2.property
      e₀.val.1.val e₀.val.1.property e₀.val.2.val e₀.val.2.property
    have ht := (le_abs_self ((q e : ℝ) - q e₀)).trans he
    linarith only [ht]
  have ht := row_density_mem_Icc q hT₂ ha hb
  change ∀ i : T, |degreeSum (fun e ↦ (q e : ℝ)) i / (T.card - 1 : ℝ) - arrayDensity q| ≤ 2 * L * h
  intro i
  have hrow := ht.2 i
  rw [Fintype.card_coe] at hrow
  exact abs_le.mpr ⟨by linarith only [hrow.1, ht.1.2], by linarith only [hrow.2, ht.1.1]⟩

end BoundedEdgeRegularSubgraphs
