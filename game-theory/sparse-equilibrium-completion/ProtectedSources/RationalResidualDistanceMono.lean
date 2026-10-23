/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCHECKED follow-on to narrow149. Actual materialized table pushes,
new residual arcs, and BFS distance monotonicity. No iteration-count or runtime
claim. Compiler checks are intentionally delegated to the serialized check owner.
-/
module
public import ProtectedSources.CachedResidualDistance
public import ProtectedSources.RationalPathSaturation
public import ProtectedSources.RationalTableAugmentation
@[expose] public section
namespace SparseCompletion

/-- Consecutive edges of an arbitrary vertex list, with no fabricated first
vertex in the empty case. -/
def rationalWalkEdges {n : ℕ} (path : List (Fin n)) : List (Fin n × Fin n) :=
  List.rec [] (fun a tail _ => rationalPathEdges a tail) path

theorem rational_walk_edges_cons {n : ℕ} (a : Fin n) (tail : List (Fin n)) :
    rationalWalkEdges (a :: tail) = rationalPathEdges a tail := rfl

theorem rational_path_edges_append_one {n : ℕ} (a : Fin n)
    (tail : List (Fin n)) (v : Fin n) :
    rationalPathEdges a (tail ++ [v]) =
      rationalPathEdges a tail ++ [(rationalPathEnd a tail, v)] := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    simp only [List.cons_append, rational_path_edges_cons,
      rational_path_end_cons, ih b]

theorem rational_walk_edges_append_one {n : ℕ} (path : List (Fin n))
    (u v : Fin n) (hend : path.getLast? = some u) :
    rationalWalkEdges (path ++ [v]) = rationalWalkEdges path ++ [(u, v)] := by
  cases path with
  | nil => cases hend
  | cons a tail =>
    have he : rationalPathEnd a tail = u := by
      exact Option.some.inj ((rational_path_end_getLast a tail).symm.trans hend)
    simpa only [List.cons_append, rational_walk_edges_cons, he] using
      rational_path_edges_append_one a tail v

/-- The completed shortest-walk length forces equality in every original
edge triangle, so every actual consecutive edge advances the BFS level by one.
The induction uses a certified walkPrefix walk, not a supplied shortest-walkPrefix
oracle. -/
theorem cached_residual_walk_edges_levels {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (path : List (Fin n)) (hw : CachedResidualWalk A s t path)
    (hd : cachedBFSDistance A s t = path.length - 1) :
    ∀ u v, (u, v) ∈ rationalWalkEdges path →
      cachedBFSDistance A s v = cachedBFSDistance A s u + 1 := by
  revert hd
  induction hw with
  | start =>
    intro hd u v he
    cases he
  | @extend a b walkPrefix hp hab ih =>
    intro hd
    have hlen := cached_residual_walk_nonempty A s a walkPrefix hp
    have hpre := cached_bfs_distance_le_walk A s a walkPrefix hp
    have htri := cached_bfs_distance_edge_triangle A s a b hab
    have hd' : cachedBFSDistance A s a = walkPrefix.length - 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hd
      omega
    have hab' : cachedBFSDistance A s b = cachedBFSDistance A s a + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hd
      omega
    intro u v he
    rw [rational_walk_edges_append_one walkPrefix a b
      (cached_residual_walk_endpoints A s a walkPrefix hp).2] at he
    rcases List.mem_append.mp he with he | he
    · exact ih hd' u v he
    · have he' : (u, v) = (a, b) := List.mem_singleton.mp he
      have hu : u = a := congrArg Prod.fst he'
      have hv : v = b := congrArg Prod.snd he'
      simpa only [hu, hv] using hab'

theorem cached_bfs_path_edges_levels {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (path : List (Fin n)) (ho : cachedBFSPath A s t = some path) :
    ∀ u v, (u, v) ∈ rationalWalkEdges path →
      cachedBFSDistance A s v = cachedBFSDistance A s u + 1 :=
  cached_residual_walk_edges_levels A s t path
    (cached_bfs_path_some_walk A s t path ho).1
    (cached_bfs_distance_of_some A s t path ho)

/-- A nonnegative path push can decrease an oriented entry only if the path
contains its reverse edge. This follows from the actual skew-net update even
for nonsimple paths; it does not assume an incidence formula. -/
theorem rational_net_push_path_le_of_reverse_absent {n : ℕ}
    (F : Fin n → Fin n → ℚ) (a : Fin n) (tail : List (Fin n))
    (δ : ℚ) (hδ : 0 ≤ δ) (u v : Fin n)
    (hnot : (v, u) ∉ rationalPathEdges a tail) :
    F u v ≤ rationalNetPushPath F a tail δ u v := by
  induction tail generalizing a with
  | nil => exact le_rfl
  | cons b tail ih =>
    have htail : (v, u) ∉ rationalPathEdges b tail := by
      intro he
      exact hnot (List.mem_cons_of_mem (a, b) he)
    have hb : ¬ (u = b ∧ v = a) := by
      rintro ⟨rfl, rfl⟩
      exact hnot List.mem_cons_self
    have hle := ih b htail
    rw [rational_net_push_path_cons]
    simp only [rationalNetPushEdge, ite_eq_right hb, sub_zero]
    split_ifs <;> linarith

/-- A positive post-update residual arc either already existed or reverses an
actual consecutive augmentation edge. Capacity feasibility and skew symmetry
are unnecessary for this local incidence fact. -/
theorem rational_net_push_path_new_residual_arc {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (a : Fin n) (tail : List (Fin n))
    (δ : ℚ) (hδ : 0 ≤ δ) (u v : Fin n)
    (hnew : 0 < C u v - rationalNetPushPath F a tail δ u v) :
    0 < C u v - F u v ∨ (v, u) ∈ rationalPathEdges a tail := by
  by_cases he : (v, u) ∈ rationalPathEdges a tail
  · exact Or.inr he
  · left
    have hle := rational_net_push_path_le_of_reverse_absent F a tail δ hδ u v he
    linarith

theorem cached_residual_arc_iff {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (u v : Fin n) :
    ((cacheResidualAdj C F).get u).get v = true ↔ 0 < C u v - F u v := by
  simp only [cacheResidualAdj, cached_vector_get_ofFn, rationalResidualAdj,
    decide_eq_true_eq]

/-- The generic comparison theorem's triangles are now earned for the actual
updated residual graph, using new-edge incidence and exact shortest-path levels.
The finite unreachable sentinel is the one defined by cachedBFSDistance. -/
theorem rational_table_push_shortest_distance_mono {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (tail : List (Fin n))
    (δ : ℚ) (hδ : 0 ≤ δ)
    (ho : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s t = some (s :: tail)) (w : Fin n) :
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s w ≤
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry (rationalTablePushPath F s tail δ))) s w := by
  apply cached_bfs_distance_mono_of_edge_triangles
  intro u v he
  have hnew := (cached_residual_arc_iff (rationalFlowTableEntry C)
    (rationalFlowTableEntry (rationalTablePushPath F s tail δ)) u v).mp he
  rw [rational_table_push_path_entry] at hnew
  rcases rational_net_push_path_new_residual_arc (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s tail δ hδ u v hnew with hold | hreverse
  · exact cached_bfs_distance_edge_triangle _ s u v
      ((cached_residual_arc_iff _ _ u v).mpr hold)
  · have hlevel := cached_bfs_path_edges_levels _ s t (s :: tail) ho v u hreverse
    omega

/-- Distances are nondecreasing after an actual successful wrapper return.
Its path and amount are extracted from the executable Option result. -/
theorem rational_augment_once_distance_mono {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out) (w : Fin n) :
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s w ≤
    cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry out.flow)) s w := by
  obtain ⟨_, hp, hcand, hm, hflow⟩ := rational_augment_once_origin C F s t out ho
  obtain ⟨hhead, _, _, hpos⟩ := hcand
  have hpath : s :: out.path.tail = out.path := by
    cases he : out.path with
    | nil => simp only [he, List.head?_nil] at hhead; cases hhead
    | cons a tail =>
      have ha : a = s := Option.some.inj (by
        simpa only [he, List.head?_cons] using hhead)
      subst a
      rfl
  have hδ : 0 < out.amount := rational_nonempty_minimum_positive
    (rationalPathResiduals (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s out.path.tail) out.amount hm hpos
  rw [hflow]
  apply rational_table_push_shortest_distance_mono C F s t out.path.tail
    out.amount (le_of_lt hδ)
  simpa only [hpath] using hp

end SparseCompletion
