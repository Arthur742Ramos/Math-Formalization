module

public import AdjacencyApproximation
public import SampledModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Finset Filter Submodule Matrix OpenProblems Approximation
open scoped Classical Topology
variable {Z : Type*} {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem complexity_on {S U : Finset Z} (A B : Z → Z → ZMod q)
    (h : ∀ x ∈ S, ∀ y ∈ U, A x y = B x y) : complexity A S U = complexity B S U := by
  suffices e : column A S '' (U : Set Z) = column B S '' (U : Set Z) by simp only [complexity,colSpace,e]
  apply Set.image_congr
  intro y hy
  exact funext fun x => h x x.2 y hy

/-- In any column set meeting the approximation cutoff, at most one cutoff's
worth of rows can agree with a low-complexity model on almost every column. -/
theorem few_agreeing_rows (q : ℕ) (hq : 3 ≤ q) [NeZero q] (τ : ℝ) (hτ : 0 < τ) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/2 ∧ ∀ D u c : ℝ, 0 < D → 0 < u → 0 < c → ∀ᶠ r : ℕ in atTop,
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B X Y : Finset (Fin N))
      (A : Fin N → Fin N → ZMod q), Core G B r u τ c → Disjoint X Y → X ⊆ B → Y ⊆ B →
      (∀ S ⊆ X, ∀ V ⊆ Y, complexity A S V ≤ D*r) → ∀ V ⊆ Y,
      (B.card:ℝ)*Real.exp (-u*r/4) ≤ V.card →
      ((X.filter fun x => (1-γ)*V.card < ((V.filter (fun y => A x y = adjMod q G x y)).card:ℝ)).card:ℝ)
        ≤ B.card*Real.exp (-u*r/4) := by
  classical
  obtain ⟨g,hg,rig⟩ := adjacency_approximation q hq τ hτ
  let γ := min (g/2) (1/2)
  have gp : 0 < γ := lt_min (by linarith) (by norm_num)
  refine ⟨γ,gp,min_le_right ..,?_⟩
  intro D u c hD hu hc
  filter_upwards [rig D u c hD hu hc] with r approx
  intro N G B X Y A core dis xb yb size V vy large
  let S := X.filter fun x => (1-γ)*V.card < ((V.filter (fun y => A x y = adjMod q G x y)).card:ℝ)
  change (S.card:ℝ) ≤ _
  by_contra! big
  have sx : S ⊆ X := filter_subset _ _
  let M : Matrix S V (ZMod q) := fun x y => A x y
  have on : complexity (extendMatrix M) S V = complexity A S V :=
    complexity_on _ _ fun x hx y hy => by simp [extendMatrix,M,hx,hy]
  have bound := approx N G B S V core (dis.mono sx vy) ⟨sx.trans xb,big.le⟩ ⟨vy.trans yb,large⟩ M
    ((complexity_extend M).symm.le.trans (on.le.trans (size S sx V vy)))
  have row (x : S) :
      ((univ.filter fun y : V => M x y ≠ adjMod q G x y).card:ℝ) ≤ γ*V.card := by
    have hit := (mem_filter.mp x.property).2
    change (1-γ)*V.card < ((V.filter (fun y => A x y = adjMod q G x y)).card:ℝ) at hit
    have card : (univ.filter (fun y : V => M x y ≠ adjMod q G x y)).card =
        (V.filter (fun y => A x y ≠ adjMod q G x y)).card := by
      rw [← card_image_of_injective _ Subtype.val_injective]
      apply congrArg Finset.card
      ext y
      simp [M,and_comm]
    rw [card]
    have part := card_filter_add_card_filter_not (s := V) (fun y => A x y = adjMod q G x y)
    have e : ((V.filter (fun y => A x y = adjMod q G x y)).card:ℝ) +
      (V.filter (fun y => A x y ≠ adjMod q G x y)).card = V.card := by exact_mod_cast part
    linarith
  have upper := bound.trans (sum_le_sum (s := (univ : Finset S)) fun x _ => row x)
  simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul] at upper
  have bp : 0 < (B.card:ℝ) := pos_of_mul_pos_left ((Real.exp_pos _).trans_le core.1) (Real.exp_pos _).le
  have st := (mul_pos bp (Real.exp_pos (-u*r/4))).trans big
  have vt := (mul_pos bp (Real.exp_pos (-u*r/4))).trans_le large
  have gap : γ < g := (min_le_left ..).trans_lt (by linarith)
  nlinarith only [upper,mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right gap st) vt]

end InducedDegreeRepetition.Restriction
