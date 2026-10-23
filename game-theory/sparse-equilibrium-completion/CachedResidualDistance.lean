/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Distances extracted from actual cached BFS paths,
genuine walk concatenation and shortest prefixes. The final comparison lemma
has an explicit edge-triangle premise; its validity for an augmented residual
graph and the Edmonds-Karp critical-arc bound remain separate obligations. -/
module
public import CachedResidualBFS
public import Mathlib.Tactic
@[expose] public section
namespace SparseCompletion

/-- A finite sentinel represents unreachable vertices. This reads the actual
cached program result; it does not minimize over an assumed set of paths.
This analysis function can rerun BFS when evaluated: it is not an O(1) getter
or a charged operation of a materialized flow-finder implementation. -/
def cachedBFSDistance {n : ℕ} (A : CachedBFSAdj n) (s v : Fin n) : ℕ :=
  Option.rec (n + 1) (fun path => path.length - 1) (cachedBFSPath A s v)

theorem cached_bfs_distance_of_some {n : ℕ} (A : CachedBFSAdj n)
    (s v : Fin n) (path : List (Fin n)) (ho : cachedBFSPath A s v = some path) :
    cachedBFSDistance A s v = path.length - 1 := by
  simp only [cachedBFSDistance, ho]

theorem cached_bfs_distance_of_none {n : ℕ} (A : CachedBFSAdj n)
    (s v : Fin n) (ho : cachedBFSPath A s v = none) :
    cachedBFSDistance A s v = n + 1 := by
  simp only [cachedBFSDistance, ho]

theorem cached_residual_walk_nonempty {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (path : List (Fin n)) (hw : CachedResidualWalk A s t path) :
    0 < path.length := by
  have hh := (cached_residual_walk_endpoints A s t path hw).1
  cases path with
  | nil => cases hh
  | cons a tail => simp only [List.length_cons]; omega

theorem cached_residual_walk_reachable {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (path : List (Fin n)) (hw : CachedResidualWalk A s t path) :
    Relation.ReflTransGen (fun u v => (A.get u).get v = true) s t := by
  induction hw with
  | start => exact Relation.ReflTransGen.refl
  | extend hwalk hedge ih => exact Relation.ReflTransGen.tail ih hedge

/-- Concatenation removes the duplicate join vertex, while executing no graph
search. Nonempty right-hand walks are earned from their walk predicate. -/
theorem cached_residual_walk_concat {n : ℕ} (A : CachedBFSAdj n)
    (s u t : Fin n) (left right : List (Fin n))
    (hl : CachedResidualWalk A s u left) (hr : CachedResidualWalk A u t right) :
    CachedResidualWalk A s t (left ++ right.tail) := by
  induction hr with
  | start => simpa only [List.tail_cons, List.append_nil] using hl
  | @extend v w walkPrefix hwalk hedge ih =>
    have hne : walkPrefix ≠ [] := by
      intro he
      have hp := cached_residual_walk_nonempty A u v walkPrefix hwalk
      simp only [he, List.length_nil] at hp
      omega
    have hext := CachedResidualWalk.extend ih hedge
    simpa only [List.tail_append_of_ne_nil hne, List.append_assoc] using hext

theorem cached_bfs_distance_source {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) :
    cachedBFSDistance A s s = 0 := by
  have hi : (cachedBFSLayers A s 0).get s = some [s] := by
    simp [cached_bfs_layers_zero, cachedBFSInitial, cached_vector_get_ofFn]
  have ho : cachedBFSPath A s s = some [s] :=
    cached_bfs_layers_keep A s s (Nat.zero_le n) [s] hi
  rw [cached_bfs_distance_of_some A s s [s] ho]
  rfl

theorem cached_bfs_distance_bound {n : ℕ} (A : CachedBFSAdj n) (s v : Fin n) :
    cachedBFSDistance A s v ≤ n + 1 := by
  cases ho : cachedBFSPath A s v with
  | none => rw [cached_bfs_distance_of_none A s v ho]
  | some path =>
    have hlen := (cached_bfs_path_some_walk A s v path ho).2
    rw [cached_bfs_distance_of_some A s v path ho]
    omega

/-- Every actual comparison walk bounds the distance of the computed output.
Reachability earns a Some payload; it is not supplied as a shortest-path oracle. -/
theorem cached_bfs_distance_le_walk {n : ℕ} (A : CachedBFSAdj n)
    (s v : Fin n) (path : List (Fin n)) (hw : CachedResidualWalk A s v path) :
    cachedBFSDistance A s v ≤ path.length - 1 := by
  obtain ⟨best, hbest, _, _, _⟩ := cached_bfs_reachable_some A s v
    (cached_residual_walk_reachable A s v path hw)
  have hlen := cached_bfs_path_shortest A s v best path hbest hw
  rw [cached_bfs_distance_of_some A s v best hbest]
  omega

/-- The triangle inequality is earned from appending the actual edge to the
actual shortest source-to-u walk. The unreachable-u sentinel case is finite. -/
theorem cached_bfs_distance_edge_triangle {n : ℕ} (A : CachedBFSAdj n)
    (s u v : Fin n) (hedge : (A.get u).get v = true) :
    cachedBFSDistance A s v ≤ cachedBFSDistance A s u + 1 := by
  cases ho : cachedBFSPath A s u with
  | none =>
    have hv := cached_bfs_distance_bound A s v
    rw [cached_bfs_distance_of_none A s u ho]
    omega
  | some path =>
    have hw := (cached_bfs_path_some_walk A s u path ho).1
    have hp := cached_residual_walk_nonempty A s u path hw
    have hv := cached_bfs_distance_le_walk A s v (path ++ [v])
      (CachedResidualWalk.extend hw hedge)
    rw [cached_bfs_distance_of_some A s u path ho]
    simp only [List.length_append, List.length_cons, List.length_nil] at hv
    omega

/-- A genuine walk prefix of the actual shortest output is itself shortest.
The proof substitutes any competing prefix into the same unchanged suffix. -/
theorem cached_bfs_shortest_prefix {n : ℕ} (A : CachedBFSAdj n)
    (s u t : Fin n) (left right : List (Fin n))
    (_hl : CachedResidualWalk A s u left) (hr : CachedResidualWalk A u t right)
    (ho : cachedBFSPath A s t = some (left ++ right.tail))
    (other : List (Fin n)) (hother : CachedResidualWalk A s u other) :
    left.length ≤ other.length := by
  have hc := cached_residual_walk_concat A s u t other right hother hr
  have hlen := cached_bfs_path_shortest A s t (left ++ right.tail)
    (other ++ right.tail) ho hc
  simp only [List.length_append] at hlen
  omega

theorem cached_bfs_distance_shortest_prefix {n : ℕ} (A : CachedBFSAdj n)
    (s u t : Fin n) (left right : List (Fin n))
    (hl : CachedResidualWalk A s u left) (hr : CachedResidualWalk A u t right)
    (ho : cachedBFSPath A s t = some (left ++ right.tail)) :
    cachedBFSDistance A s u = left.length - 1 := by
  obtain ⟨best, hbest, hw, _, _⟩ := cached_bfs_reachable_some A s u
    (cached_residual_walk_reachable A s u left hl)
  have hle := cached_bfs_path_shortest A s u best left hbest hl
  have hge := cached_bfs_shortest_prefix A s u t left right hl hr ho best hw
  rw [cached_bfs_distance_of_some A s u best hbest]
  omega

/-- Along an actual shortest output, a genuine prefix edge advances distance
by exactly one. No externally supplied distance or Antitone premise is used. -/
theorem cached_bfs_distance_shortest_prefix_edge {n : ℕ} (A : CachedBFSAdj n)
    (s u v t : Fin n) (left right : List (Fin n))
    (hl : CachedResidualWalk A s u left) (hedge : (A.get u).get v = true)
    (hr : CachedResidualWalk A v t right)
    (ho : cachedBFSPath A s t = some ((left ++ [v]) ++ right.tail)) :
    cachedBFSDistance A s v = cachedBFSDistance A s u + 1 := by
  have hleftv : CachedResidualWalk A s v (left ++ [v]) :=
    CachedResidualWalk.extend hl hedge
  have hrightu : CachedResidualWalk A u t ([u, v] ++ right.tail) :=
    cached_residual_walk_concat A u v t [u, v] right
      (CachedResidualWalk.extend CachedResidualWalk.start hedge) hr
  have ho' : cachedBFSPath A s t = some (left ++ ([u, v] ++ right.tail).tail) := by
    simpa only [List.cons_append, List.nil_append, List.tail_cons, List.append_assoc]
      using ho
  have hu := cached_bfs_distance_shortest_prefix A s u t left
    ([u, v] ++ right.tail) hl hrightu ho'
  have hv := cached_bfs_distance_shortest_prefix A s v t (left ++ [v]) right hleftv hr ho
  have hp := cached_residual_walk_nonempty A s u left hl
  rw [hu, hv]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Generic potential bound along a genuine walk. This does not assert that
any particular augmented graph satisfies its edge premise. -/
theorem cached_walk_potential_bound {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (d : Fin n → ℕ) (hs : d s = 0)
    (hedge : ∀ u v, (A.get u).get v = true → d v ≤ d u + 1)
    (path : List (Fin n)) (hw : CachedResidualWalk A s t path) :
    d t ≤ path.length - 1 := by
  induction hw with
  | start => simpa only [List.length_cons, List.length_nil] using (le_of_eq hs)
  | @extend u v walkPrefix hwalk huv ih =>
    have hp := cached_residual_walk_nonempty A s u walkPrefix hwalk
    have he := hedge u v huv
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- A conditional graph comparison theorem for the later residual-update proof.
No claim is made here that the edge-triangle premise has been earned after
augmentation: that needs the new-edge/reverse-path incidence argument. -/
theorem cached_bfs_distance_mono_of_edge_triangles {n : ℕ}
    (Aold Anew : CachedBFSAdj n) (s : Fin n)
    (hedge : ∀ u v, (Anew.get u).get v = true →
      cachedBFSDistance Aold s v ≤ cachedBFSDistance Aold s u + 1)
    (v : Fin n) : cachedBFSDistance Aold s v ≤ cachedBFSDistance Anew s v := by
  cases ho : cachedBFSPath Anew s v with
  | none =>
    rw [cached_bfs_distance_of_none Anew s v ho]
    exact cached_bfs_distance_bound Aold s v
  | some path =>
    have hw := (cached_bfs_path_some_walk Anew s v path ho).1
    have hp := cached_walk_potential_bound Anew s v (cachedBFSDistance Aold s)
      (cached_bfs_distance_source Aold s) hedge path hw
    rwa [cached_bfs_distance_of_some Anew s v path ho]

end SparseCompletion
