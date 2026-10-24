module
public import Mycielski.FusionStep

public section
namespace Mycielski
open Set TopologicalSpace Metric CantorScheme Filter Function
open scoped Topology ENNReal

abbrev Node (n : ℕ) := List.Vector Bool n

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [PerfectSpace X]

structure Stage (R : ℕ → Set (X × X)) (u : ℕ → ℝ≥0∞) (n : ℕ) where
  cell : Node n → Set X
  open_cell : ∀ s, IsOpen (cell s)
  nonempty_cell : ∀ s, (cell s).Nonempty
  separate : ∀ s t, s ≠ t → Disjoint (closure (cell s)) (closure (cell t))
  small : ∀ s, 0 < n → ediam (cell s) ≤ u n
  relation : ∀ s t, s ≠ t → ∀ k < n, closure (cell s) ×ˢ closure (cell t) ⊆ R k

@[expose] def initialStage (R : ℕ → Set (X × X)) (u : ℕ → ℝ≥0∞)
    {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty) : Stage R u 0 where
  cell _ := U
  open_cell _ := hU
  nonempty_cell _ := hneU
  separate s t h := (h (Subsingleton.elim s t)).elim
  small _ h := by omega
  relation _ _ _ _ h := by omega

theorem stage_refinement {R : ℕ → Set (X × X)} {u : ℕ → ℝ≥0∞}
    (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k))
    (hu : ∀ n, 0 < u n) {n : ℕ} (S : Stage R u n) :
    ∃ T : Stage R u (n + 1), ∀ s : Node (n + 1), closure (T.cell s) ⊆ S.cell s.tail := by
  let W : Set (X × X) := ⋂ k : Fin (n + 1), R k
  have hoW : IsOpen W := isOpen_iInter_of_finite fun k => hoR k
  have hdW : Dense W := dense_iInter_of_isOpen (fun k => hoR k) (fun k => hdR k)
  obtain ⟨T, hT, hcross⟩ := finite_refinement (fun s : Node (n + 1) => S.cell s.tail)
    (fun s => S.open_cell s.tail) (fun s => S.nonempty_cell s.tail) hoW hdW (hu (n + 1))
  refine ⟨⟨T, fun s => (hT s).1, fun s => (hT s).2.1,
    fun s t hst => (hcross s t hst).1,
    fun s _ => (hT s).2.2.2, ?_⟩, fun s => (hT s).2.2.1⟩
  intro s t hst k hk p hp
  exact mem_iInter.mp ((hcross s t hst).2 hp) (⟨k, hk⟩ : Fin (n + 1))

@[expose] noncomputable def stages {R : ℕ → Set (X × X)} {u : ℕ → ℝ≥0∞}
    (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k)) (hu : ∀ n, 0 < u n)
    {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty) : ∀ n, Stage R u n
  | 0 => initialStage R u hU hneU
  | n + 1 => (stage_refinement hoR hdR hu (stages hoR hdR hu hU hneU n)).choose

theorem stages_refine {R : ℕ → Set (X × X)} {u : ℕ → ℝ≥0∞}
    (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k)) (hu : ∀ n, 0 < u n)
    {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty) (n : ℕ) (s : Node (n + 1)) :
    closure ((stages hoR hdR hu hU hneU (n + 1)).cell s) ⊆
      (stages hoR hdR hu hU hneU n).cell s.tail :=
  (stage_refinement hoR hdR hu (stages hoR hdR hu hU hneU n)).choose_spec s

end Mycielski
