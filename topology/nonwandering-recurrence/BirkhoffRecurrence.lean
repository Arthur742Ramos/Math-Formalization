module
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Tactic

@[expose] public section
open Set Filter Function TopologicalSpace
open scoped Topology
namespace CategoryRecurrence

/-- Every nonempty open set has an actual positive self-return. -/
abbrev Nonwandering {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → ∃ n : ℕ, 0 < n ∧ ∃ x ∈ U, f^[n] x ∈ U

/-- Arbitrarily late returns to every open neighborhood of the point. -/
abbrev Recurrent {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ f^[n] x ∈ U

/-- A countable positive scale tending to zero. -/
noncomputable def radius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- An actual late return, rather than the vacuous time-zero condition. -/
def ReturnStage {X : Type*} [MetricSpace X] (f : X → X) (k N : ℕ) : Set X :=
  {x | ∃ n : ℕ, N < n ∧ dist (f^[n] x) x < radius k}

theorem radius_pos (k : ℕ) : 0 < radius k := by
  unfold radius
  positivity

/-- Repeatedly shrink an open return pair to obtain arbitrarily late self-returns. -/
theorem nonwandering_iff_late_returns {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) : Nonwandering f ↔
    ∀ U : Set X, IsOpen U → U.Nonempty → ∀ N : ℕ,
      ∃ n : ℕ, N < n ∧ ∃ x ∈ U, f^[n] x ∈ U := by
  constructor
  · intro hw U hU hnU N
    induction N with
    | zero => exact hw U hU hnU
    | succ N ih =>
      obtain ⟨n, hn, x, hx, hfx⟩ := ih
      let V : Set X := U ∩ f^[n] ⁻¹' U
      have hV : IsOpen V := hU.inter (hU.preimage (hf.iterate n))
      have hnV : V.Nonempty := ⟨x, hx, hfx⟩
      obtain ⟨m, hm, y, hy, hmy⟩ := hw V hV hnV
      refine ⟨n + m, by omega, y, hy.1, ?_⟩
      simpa only [mem_preimage, iterate_add_apply] using hmy.2
  · intro h U hU hnU
    exact h U hU hnU 0

/-- Countably many metric scales encode all open-neighborhood return requirements. -/
theorem recurrent_iff_return_stages {X : Type*} [MetricSpace X]
    (f : X → X) (x : X) : Recurrent f x ↔ ∀ k N : ℕ, x ∈ ReturnStage f k N := by
  constructor
  · intro hx k N
    exact hx (Metric.ball x (radius k)) Metric.isOpen_ball
      (Metric.mem_ball_self (radius_pos k)) N
  · intro hx U hU hxU N
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨n, hn, hdist⟩ := hx k N
    exact ⟨n, hn, hball (lt_trans hdist hk)⟩

theorem isOpen_return_stage {X : Type*} [MetricSpace X]
    (f : X → X) (hf : Continuous f) (k N : ℕ) : IsOpen (ReturnStage f k N) := by
  rw [show ReturnStage f k N = ⋃ n : ℕ, ⋃ (_h : N < n),
      {x | dist (f^[n] x) x < radius k} by ext x; simp [ReturnStage]]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ =>
    isOpen_lt ((hf.iterate n).dist continuous_id) continuous_const

/-- The recurrent-point set itself is G-delta, independently of nonwandering or Baire assumptions. -/
theorem isGdelta_recurrent {X : Type*} [MetricSpace X]
    (f : X → X) (hf : Continuous f) : IsGδ {x : X | Recurrent f x} := by
  rw [show {x : X | Recurrent f x} = ⋂ k : ℕ, ⋂ N : ℕ, ReturnStage f k N by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    exact recurrent_iff_return_stages f x]
  exact IsGδ.iInter fun k => IsGδ.iInter_of_isOpen fun N => isOpen_return_stage f hf k N

/-- A late return within one small ball is a small displacement in every prescribed open set. -/
theorem dense_return_stage {X : Type*} [MetricSpace X] (f : X → X)
    (hf : Continuous f) (hw : Nonwandering f) (k N : ℕ) : Dense (ReturnStage f k N) := by
  apply dense_iff_inter_open.mpr
  intro U hU hnU
  obtain ⟨x, hx⟩ := hnU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let r : ℝ := min δ (radius k / 2)
  have hr : 0 < r := lt_min hδ (half_pos (radius_pos k))
  obtain ⟨n, hn, y, hy, hfy⟩ := (nonwandering_iff_late_returns f hf).mp hw
    (Metric.ball x r) Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr⟩ N
  refine ⟨y, hball ?_, n, hn, ?_⟩
  · exact lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)
  · calc
      dist (f^[n] y) y ≤ dist (f^[n] y) x + dist x y := dist_triangle _ _ _
      _ < r + r := add_lt_add (Metric.mem_ball.mp hfy)
        (by simpa only [dist_comm] using Metric.mem_ball.mp hy)
      _ ≤ radius k := by
        have h : r ≤ radius k / 2 := min_le_right _ _
        linarith

/-- The countable open dense return stages give residual recurrence without any Baire premise. -/
theorem residual_recurrent {X : Type*} [MetricSpace X] (f : X → X)
    (hf : Continuous f) (hw : Nonwandering f) : {x : X | Recurrent f x} ∈ residual X := by
  have hh : {x : X | ∀ k N : ℕ, x ∈ ReturnStage f k N} ∈ residual X :=
    eventually_countable_forall.mpr fun k => eventually_countable_forall.mpr fun N =>
      residual_of_dense_open (isOpen_return_stage f hf k N) (dense_return_stage f hf hw k N)
  refine mem_of_superset hh ?_
  intro x hx
  exact (recurrent_iff_return_stages f x).mpr hx

/-- Baire category characterizes nonwandering maps by density of their actual recurrent points. -/
theorem nonwandering_iff_dense_recurrent {X : Type*} [MetricSpace X] [BaireSpace X]
    (f : X → X) (hf : Continuous f) : Nonwandering f ↔ Dense {x : X | Recurrent f x} := by
  constructor
  · intro hw
    exact dense_of_mem_residual (residual_recurrent f hf hw)
  · intro hd U hU hnU
    obtain ⟨x, hxU, hxR⟩ := dense_iff_inter_open.mp hd U hU hnU
    obtain ⟨n, hn, hfn⟩ := hxR U hU hxU 0
    exact ⟨n, hn, x, hxU, hfn⟩

end CategoryRecurrence
