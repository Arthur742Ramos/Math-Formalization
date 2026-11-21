module

public import RigidityEstimate
public import GraphMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.OpenProblems

open Finset Filter Approximation
open scoped Classical Topology

/-- Lemma 5. A low-error approximation would admit a constant rectangle above
the cut threshold on which the error is smaller than the cut-density lower bound. -/
theorem adjacency_approximation : AdjacencyApproximation := by
  classical
  intro q hq inst τ hτ
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  let γ := min (1/16:ℝ) (τ/(8*q))
  have gp : 0 < γ := lt_min (by norm_num) (by positivity)
  have err : 4*γ*q < τ := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ)<8*q)).mp (min_le_right (1/16:ℝ) (τ/(8*q)))
    dsimp [γ]
    linarith
  refine ⟨γ,gp,?_⟩
  intro D u c hD hu hc
  filter_upwards [rigidity_estimate hq γ (3*u/4) D gp (min_le_left ..) (by positivity) hD] with r rect
  intro N G B X Y core dis hX hY A comp
  let E := extendMatrix A
  rw [← errors_extend]
  by_contra! low
  have cutpos : 0 < (B.card:ℝ)*Real.exp (-u*r) := (Real.exp_pos _).trans_le core.1
  have bp : (0:ℝ)<B.card := pos_of_mul_pos_left cutpos (Real.exp_pos _).le
  have xp : (0:ℝ)<X.card := (mul_pos bp (Real.exp_pos _)).trans_le hX.2
  have yp : (0:ℝ)<Y.card := (mul_pos bp (Real.exp_pos _)).trans_le hY.2
  obtain ⟨R,rx,V,vy,t,hr,hv,con,bound⟩ := rect (Fin N) (Fin N) E (adjMod q G) X Y
    (card_pos.mp (by exact_mod_cast xp)) (card_pos.mp (by exact_mod_cast yp))
    (fun x _ y _ => by unfold adjMod; split <;> simp) low.le ((complexity_extend A).le.trans comp)
  have threshold {m k : ℕ} (hm : (B.card:ℝ)*Real.exp (-u*r/4) ≤ m)
      (hk : Real.exp (-(3*u/4)*r)*m ≤ k) : (B.card:ℝ)*Real.exp (-u*r) ≤ k := by
    apply le_trans _ ((mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le).trans hk)
    apply le_of_eq
    rw [mul_left_comm,← Real.exp_add]
    ring_nf
  have lr := threshold hX.2 hr
  have lv := threshold hY.2 hv
  have neq := constant_errors hq G core.2 (rx.trans hX.1) (vy.trans hY.1) (dis.mono rx vy) lr lv E t con
  exact (not_le_of_gt (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right err (cutpos.trans_le lr))
    (cutpos.trans_le lv))) (neq.trans bound)

end InducedDegreeRepetition.OpenProblems
