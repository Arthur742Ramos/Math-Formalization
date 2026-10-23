/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCHECKED. Critical arcs and level recurrence for genuine successful
augmentation traces. A trace premise consists only of actual Option-return and
materialized next-state equations. No distance, progress, count, or termination
conclusion is supplied as a trace field or hypothesis.
-/
module
public import RationalResidualDistanceMono
@[expose] public section
namespace SparseCompletion

theorem rational_augment_once_path_source {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out) :
    s :: out.path.tail = out.path := by
  have hhead := (rational_augment_once_origin C F s t out ho).2.2.1.1
  cases he : out.path with
  | nil => simp only [he, List.head?_nil] at hhead; cases hhead
  | cons a tail =>
    have ha : a = s := Option.some.inj (by
      simpa only [he, List.head?_cons] using hhead)
    subst a
    rfl

theorem rational_augment_once_amount_positive {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out) : 0 < out.amount := by
  obtain ⟨_, _, hcand, hm, _⟩ := rational_augment_once_origin C F s t out ho
  exact rational_nonempty_minimum_positive
    (rationalPathResiduals (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s out.path.tail) out.amount hm hcand.2.2.2

/-- Every successful actual attempt supplies a saturated actual path edge.
This is an existential witness extracted from the computed bottleneck. -/
theorem rational_augment_once_critical_arc {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out) :
    ∃ u v, (u, v) ∈ rationalWalkEdges out.path ∧
      rationalFlowTableEntry out.flow u v = rationalFlowTableEntry C u v := by
  obtain ⟨_, _, hcand, hm, hflow⟩ := rational_augment_once_origin C F s t out ho
  have hpath := rational_augment_once_path_source C F s t out ho
  have hnd : (s :: out.path.tail).Nodup := by
    simpa only [hpath] using hcand.2.2.1
  obtain ⟨u, v, he, _, hsat⟩ := rational_path_bottleneck_saturates
    (rationalFlowTableEntry C) (rationalFlowTableEntry F) s out.path.tail hnd
    out.amount hm
  refine ⟨u, v, ?_, ?_⟩
  · have he' : (u, v) ∈ rationalWalkEdges (s :: out.path.tail) := he
    rw [hpath] at he'
    exact he'
  · rw [hflow, rational_table_push_path_entry]
    exact hsat

theorem rational_augment_once_edge_levels {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out)
    (u v : Fin n) (he : (u, v) ∈ rationalWalkEdges out.path) :
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s v =
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s u + 1 :=
  cached_bfs_path_edges_levels _ s t out.path
    (rational_augment_once_origin C F s t out ho).2.1 u v he

theorem cached_residual_walk_edges_arcs {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (path : List (Fin n)) (hw : CachedResidualWalk A s t path) :
    ∀ u v, (u, v) ∈ rationalWalkEdges path → (A.get u).get v = true := by
  induction hw with
  | start => intro u v he; cases he
  | @extend a b walkPrefix hp hab ih =>
    intro u v he
    rw [rational_walk_edges_append_one walkPrefix a b
      (cached_residual_walk_endpoints A s a walkPrefix hp).2] at he
    rcases List.mem_append.mp he with he | he
    · exact ih u v he
    · have he' : (u, v) = (a, b) := List.mem_singleton.mp he
      have hu : u = a := congrArg Prod.fst he'
      have hv : v = b := congrArg Prod.snd he'
      simpa only [hu, hv] using hab

theorem rational_augment_once_edge_residual {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out)
    (u v : Fin n) (he : (u, v) ∈ rationalWalkEdges out.path) :
    0 < rationalFlowTableEntry C u v - rationalFlowTableEntry F u v := by
  have hp := (rational_augment_once_origin C F s t out ho).2.1
  have hw := (cached_bfs_path_some_walk _ s t out.path hp).1
  exact (cached_residual_arc_iff _ _ u v).mp
    (cached_residual_walk_edges_arcs _ s t out.path hw u v he)

theorem rational_augment_once_entry_le_of_reverse_absent {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out)
    (u v : Fin n) (he : (v, u) ∉ rationalWalkEdges out.path) :
    rationalFlowTableEntry F u v ≤ rationalFlowTableEntry out.flow u v := by
  have hpath := rational_augment_once_path_source C F s t out ho
  have hnot : (v, u) ∉ rationalPathEdges s out.path.tail := by
    intro hmem
    have he' : (v, u) ∈ rationalWalkEdges (s :: out.path.tail) := hmem
    rw [hpath] at he'
    exact he he'
  rw [(rational_augment_once_origin C F s t out ho).2.2.2.2,
    rational_table_push_path_entry]
  exact rational_net_push_path_le_of_reverse_absent _ s out.path.tail
    out.amount (le_of_lt (rational_augment_once_amount_positive C F s t out ho)) u v hnot

/-- A finite successful execution is described only by actual program
equations. Distance monotonicity at arbitrary trace times is derived. -/
theorem rational_successful_trace_distance_mono {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (k : ℕ) (F : ℕ → RationalFlowTable n)
    (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (i j : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (v : Fin n) :
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (F i))) s v ≤
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (F j))) s v := by
  have haux : ∀ d, i + d ≤ k →
      cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (F i))) s v ≤
      cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (F (i + d)))) s v := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have hlt : i + d < k := by omega
      have hstep := rational_augment_once_distance_mono C (F (i + d)) s t
        (out (i + d)) (hreturn (i + d) hlt) v
      rw [← hnext (i + d) hlt] at hstep
      exact le_trans (ih (by omega)) hstep
  have he : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa only [he] using haux (j - i) (by omega)

/-- If an oriented entry strictly decreases along a genuine execution segment,
some actual returned path in that segment traverses the reverse edge. -/
theorem rational_successful_trace_reverse_of_decrease {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (k : ℕ)
    (F : ℕ → RationalFlowTable n) (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (i j : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (u v : Fin n)
    (hdec : rationalFlowTableEntry (F j) u v < rationalFlowTableEntry (F i) u v) :
    ∃ r, i ≤ r ∧ r < j ∧ (v, u) ∈ rationalWalkEdges (out r).path := by
  by_contra hn
  have habsent : ∀ r, i ≤ r → r < j →
      (v, u) ∉ rationalWalkEdges (out r).path := by
    intro r hir hrj he
    exact hn ⟨r, hir, hrj, he⟩
  have haux : ∀ d, i + d ≤ j →
      rationalFlowTableEntry (F i) u v ≤ rationalFlowTableEntry (F (i + d)) u v := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have hrj : i + d < j := by omega
      have hrk : i + d < k := by omega
      have hstep := rational_augment_once_entry_le_of_reverse_absent C (F (i + d)) s t
        (out (i + d)) (hreturn (i + d) hrk) u v
        (habsent (i + d) (by omega) hrj)
      rw [← hnext (i + d) hrk] at hstep
      exact le_trans (ih (by omega)) hstep
  have he : i + (j - i) = j := Nat.add_sub_of_le hij
  have hle : rationalFlowTableEntry (F i) u v ≤ rationalFlowTableEntry (F j) u v := by
    simpa only [he] using haux (j - i) (by omega)
  exact (not_lt_of_ge hle) hdec

/-- Two actual opposite traversals force a level increase by two. Monotonicity
between the two return states and the final state is earned from the trace. -/
theorem rational_successful_trace_opposite_level_gap {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (k : ℕ)
    (F : ℕ → RationalFlowTable n) (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (i r j : ℕ) (hir : i ≤ r) (hrj : r ≤ j) (hjk : j ≤ k) (hrk : r < k)
    (u v : Fin n) (hforward : (u, v) ∈ rationalWalkEdges (out i).path)
    (hreverse : (v, u) ∈ rationalWalkEdges (out r).path) :
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (F i))) s u + 2 ≤
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (F j))) s u := by
  have hik : i < k := by omega
  have hi := rational_augment_once_edge_levels C (F i) s t (out i)
    (hreturn i hik) u v hforward
  have hr := rational_augment_once_edge_levels C (F r) s t (out r)
    (hreturn r hrk) v u hreverse
  have hmono1 := rational_successful_trace_distance_mono C s t k F out hreturn hnext
    i r hir (by omega) v
  have hmono2 := rational_successful_trace_distance_mono C s t k F out hreturn hnext
    r j hrj hjk u
  omega

/-- Reuse after actual saturation forces an intervening reverse traversal,
and hence raises the same oriented arc's tail level by at least two. Neither
the intervening reversal nor the level increase is assumed. -/
theorem rational_successful_trace_critical_recurrence {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (k : ℕ)
    (F : ℕ → RationalFlowTable n) (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (i j : ℕ) (hij : i < j) (hjk : j < k) (u v : Fin n)
    (hfirst : (u, v) ∈ rationalWalkEdges (out i).path)
    (hsat : rationalFlowTableEntry (out i).flow u v = rationalFlowTableEntry C u v)
    (hlater : (u, v) ∈ rationalWalkEdges (out j).path) :
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (F i))) s u + 2 ≤
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (F j))) s u := by
  have hik : i < k := by omega
  have hres := rational_augment_once_edge_residual C (F j) s t (out j)
    (hreturn j hjk) u v hlater
  have he : rationalFlowTableEntry (F (i + 1)) u v = rationalFlowTableEntry C u v := by
    rw [hnext i hik, hsat]
  have hdec : rationalFlowTableEntry (F j) u v <
      rationalFlowTableEntry (F (i + 1)) u v := by
    rw [he]
    linarith
  obtain ⟨r, hir, hrj, hreverse⟩ := rational_successful_trace_reverse_of_decrease
    C s t k F out hreturn hnext (i + 1) j (by omega) (by omega) u v hdec
  exact rational_successful_trace_opposite_level_gap C s t k F out hreturn hnext
    i r j (by omega) (by omega) (by omega) (by omega) u v hfirst hreverse

end SparseCompletion
