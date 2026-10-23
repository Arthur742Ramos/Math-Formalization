/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately.
First-discovery simplicity of the actual cached BFS tables. No cycle-erasure
oracle, assumed shortest-path simplicity, max-flow or cost claim. -/
module
public import ProtectedSources.CachedResidualBFS
public import Mathlib.Tactic
@[expose] public section
namespace SparseCompletion

/-- In addition to simplicity, every label on a stored walk has already been
discovered in this same table. The second conjunct earns simplicity when a new
endpoint is appended, rather than assuming it as an input. -/
def CachedBFSSimpleTable {n : ℕ} (table : CachedBFSPaths n) : Prop :=
  ∀ v path, table.get v = some path →
    path.Nodup ∧ ∀ u ∈ path, table.get u ≠ none

theorem cached_bfs_step_discovered {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (u : Fin n) (hu : prev.get u ≠ none) :
    (cachedBFSStep A prev).get u ≠ none := by
  cases hp : prev.get u with
  | none => exact False.elim (hu hp)
  | some path =>
    rw [cached_bfs_step_keep A prev u path hp]
    simp

theorem cached_bfs_initial_simple {n : ℕ} (s : Fin n) :
    CachedBFSSimpleTable (cachedBFSInitial s) := by
  intro v path ho
  by_cases hv : v = s
  · subst v
    have he : some [s] = some path := by
      simpa [cachedBFSInitial, cached_vector_get_ofFn] using ho
    have hpath : path = [s] := (Option.some.inj he).symm
    subst path
    constructor
    · simp
    · intro u hu
      have hus : u = s := by simpa only [List.mem_singleton] using hu
      subst u
      simp only [cachedBFSInitial, cached_vector_get_ofFn]
      simp
  · have he : (none : Option (List (Fin n))) = some path := by
      simpa only [cachedBFSInitial, cached_vector_get_ofFn, ite_eq_right hv] using ho
    cases he

theorem cached_bfs_step_simple {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (hprev : CachedBFSSimpleTable prev) :
    CachedBFSSimpleTable (cachedBFSStep A prev) := by
  intro v path ho
  cases hp : prev.get v with
  | some oldPath =>
    have he : some oldPath = some path := by
      simpa only [cachedBFSStep, cached_vector_get_ofFn, hp] using ho
    have hpath : oldPath = path := Option.some.inj he
    subst path
    obtain ⟨hnd, hmem⟩ := hprev v oldPath hp
    exact ⟨hnd, fun u hu => cached_bfs_step_discovered A prev u (hmem u hu)⟩
  | none =>
    have he : cachedBFSExtend A prev v (List.finRange n) = some path := by
      simpa only [cachedBFSStep, cached_vector_get_ofFn, hp] using ho
    obtain ⟨u, _, walkPrefix, hprefix, _, hpath⟩ :=
      cached_bfs_extend_some A prev v (List.finRange n) path he
    obtain ⟨hnd, hmem⟩ := hprev u walkPrefix hprefix
    have hvnew : v ∉ walkPrefix := by
      intro hv
      exact hmem v hv hp
    subst path
    constructor
    · apply List.nodup_append.mpr
      refine ⟨hnd, by simp, ?_⟩
      intro x hx y hy
      have hy : y = v := by simpa only [List.mem_singleton] using hy
      subst y
      intro hxv
      exact hvnew (hxv ▸ hx)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact cached_bfs_step_discovered A prev x (hmem x hx)
      · have hxv : x = v := by simpa only [List.mem_singleton] using hx
        subst x
        rw [ho]
        simp

theorem cached_bfs_layers_simple {n : ℕ} (A : CachedBFSAdj n)
    (s : Fin n) (k : ℕ) : CachedBFSSimpleTable (cachedBFSLayers A s k) := by
  induction k with
  | zero => exact cached_bfs_initial_simple s
  | succ k ih =>
    rw [cached_bfs_layers_succ]
    exact cached_bfs_step_simple A (cachedBFSLayers A s k) ih

/-- The actual returned list has no repeated vertex. This includes the
source-equals-target singleton; no positive path-length hypothesis is hidden. -/
theorem cached_bfs_path_nodup {n : ℕ} (A : CachedBFSAdj n)
    (s t : Fin n) (path : List (Fin n))
    (ho : cachedBFSPath A s t = some path) : path.Nodup := by
  exact (cached_bfs_layers_simple A s n t path ho).1

end SparseCompletion
