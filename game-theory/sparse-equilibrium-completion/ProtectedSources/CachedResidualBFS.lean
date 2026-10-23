/- AI-assisted formalization under the repository Apache-2.0 license.
Cached finite Boolean adjacency and discovered-walk vectors, with reachability,
shortest-walk and predecessor correctness. No max-flow or machine/bit-cost claim. -/
module
public import ProtectedSources.RationalResidualReach
public import Init.Data.Vector.OfFn
@[expose] public section
namespace SparseCompletion

abbrev CachedBFSAdj (n : ℕ) := Vector (Vector Bool n) n
abbrev CachedBFSPaths (n : ℕ) := Vector (Option (List (Fin n))) n

/-- Vector indexing of a constructed table preserves the original finite index. -/
theorem cached_vector_get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  simp only [Vector.getElem_ofFn]

/-- Actual graph data, not a recursively reevaluated functional layer. -/
def cacheResidualAdj {n : ℕ} (C F : Fin n → Fin n → ℚ) : CachedBFSAdj n :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => rationalResidualAdj C F u v))

/-- Keep the first discovered complete walk to each vertex. -/
def cachedBFSInitial {n : ℕ} (s : Fin n) : CachedBFSPaths n :=
  Vector.ofFn (fun v => if v=s then some [s] else none)

/-- Search predecessor labels against the same stored previous-layer vector.
Unit-thunked public recursors avoid eager evaluation of an unused tail branch.
This helper does not invoke cachedBFSLayers or recursively rebuild a layer. -/
def cachedBFSExtend {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) (labels : List (Fin n)) : Option (List (Fin n)) :=
  List.rec (fun _ : Unit => none)
    (fun u _ ih _ =>
      Option.rec (fun _ : Unit => ih ())
        (fun path _ =>
          Bool.rec (fun _ : Unit => ih ()) (fun _ : Unit => some (path++[v]))
            ((A.get u).get v) ())
        (prev.get u) ()) labels ()

/-- One simultaneous layer: all lookups read prev, rather than a recursively
computed prior-layer function or partially updated current-layer table. -/
def cachedBFSStep {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n) : CachedBFSPaths n :=
  Vector.ofFn (fun v =>
    Option.rec (fun _ : Unit => cachedBFSExtend A prev v (List.finRange n))
      (fun path _ => some path) (prev.get v) ())

def cachedBFSLayers {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ) : CachedBFSPaths n :=
  Nat.rec (cachedBFSInitial s) (fun _ prev => cachedBFSStep A prev) k

/-- Finite n-layer walk result, with correctness proved below. -/
def cachedBFSPath {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n) : Option (List (Fin n)) :=
  (cachedBFSLayers A s n).get t

/-- Actual returned path together with its predecessor at the target, if any.
The source-only singleton walk has no predecessor. Computed from one BFS call. -/
def cachedBFSResult {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n) :
    Option (List (Fin n) × Option (Fin n)) :=
  (cachedBFSPath A s t).map (fun path => (path, path.reverse.tail.head?))

def cachedRationalResidualPath {n : ℕ} (C F : Fin n → Fin n → ℚ) (s t : Fin n) :
    Option (List (Fin n) × Option (Fin n)) :=
  let A := cacheResidualAdj C F
  cachedBFSResult A s t

/-- Literal finite walk semantics: zero edges or append one actual stored edge.
This is an input-independent predicate, not an assumed correctness oracle. -/
inductive CachedResidualWalk {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) :
    Fin n → List (Fin n) → Prop
  | start : CachedResidualWalk A s s [s]
  | extend {u v : Fin n} {path : List (Fin n)} :
      CachedResidualWalk A s u path → (A.get u).get v=true →
      CachedResidualWalk A s v (path++[v])

theorem cached_bfs_layers_zero {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) :
    cachedBFSLayers A s 0=cachedBFSInitial s := rfl

theorem cached_bfs_layers_succ {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ) :
    cachedBFSLayers A s (Nat.succ k)=cachedBFSStep A (cachedBFSLayers A s k) := rfl

theorem cached_bfs_extend_nil {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) : cachedBFSExtend A prev v []=none := rfl

/-- Soundness of the concrete predecessor search, with the actual stored walkPrefix. -/
theorem cached_bfs_extend_some {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) (labels : List (Fin n)) (w : List (Fin n))
    (ho : cachedBFSExtend A prev v labels=some w) :
    ∃ u ∈ labels, ∃ path, prev.get u=some path ∧
      (A.get u).get v=true ∧ w=path++[v] := by
  revert ho
  induction labels with
  | nil => intro ho; simp only [cached_bfs_extend_nil] at ho; cases ho
  | cons u us ih =>
    intro ho
    cases hp : prev.get u with
    | none =>
      have ht : cachedBFSExtend A prev v us=some w := by
        simpa only [cachedBFSExtend, hp] using ho
      obtain ⟨a, ha, path, hpath, hedge, hw⟩ := ih ht
      exact ⟨a, List.mem_cons_of_mem u ha, path, hpath, hedge, hw⟩
    | some path =>
      cases he : (A.get u).get v with
      | false =>
        have ht : cachedBFSExtend A prev v us=some w := by
          simpa only [cachedBFSExtend, hp, he] using ho
        obtain ⟨a, ha, p, hpath, hedge, hw⟩ := ih ht
        exact ⟨a, List.mem_cons_of_mem u ha, p, hpath, hedge, hw⟩
      | true =>
        have hw : some (path++[v])=some w := by
          simpa only [cachedBFSExtend, hp, he] using ho
        exact ⟨u, List.mem_cons_self, path, hp, he, (Option.some.inj hw).symm⟩

/-- Failure is exactly absence of an incoming edge from an already discovered
vertex. This is a finite, checkable condition, not a reachability assumption. -/
theorem cached_bfs_extend_none_iff {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) (labels : List (Fin n)) :
    cachedBFSExtend A prev v labels=none ↔
      ∀ u ∈ labels, prev.get u=none ∨ (A.get u).get v=false := by
  induction labels with
  | nil => simp [cachedBFSExtend]
  | cons u us ih =>
    cases hp : prev.get u with
    | none => simpa [cachedBFSExtend, hp] using ih
    | some path =>
      cases he : (A.get u).get v <;> simp_all [cachedBFSExtend]

/-- Concrete invariant carried by every stored walk. The length counts vertices;
therefore the corresponding edge count is at most k. -/
def CachedBFSTableValid {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ)
    (table : CachedBFSPaths n) : Prop :=
  ∀ v path, table.get v=some path →
    CachedResidualWalk A s v path ∧ path.length ≤ k+1

theorem cached_bfs_initial_valid {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) :
    CachedBFSTableValid A s 0 (cachedBFSInitial s) := by
  intro v path ho
  by_cases hv : v=s
  · subst v
    have hp : path=[s] := by
      have h : some [s]=some path := by simpa [cachedBFSInitial, cached_vector_get_ofFn] using ho
      exact (Option.some.inj h).symm
    subst path
    exact ⟨CachedResidualWalk.start, by simp⟩
  · simp [cachedBFSInitial, cached_vector_get_ofFn, hv] at ho

theorem cached_bfs_step_valid {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ)
    (prev : CachedBFSPaths n) (hprev : CachedBFSTableValid A s k prev) :
    CachedBFSTableValid A s (Nat.succ k) (cachedBFSStep A prev) := by
  intro v path ho
  cases hp : prev.get v with
  | none =>
    have he : cachedBFSExtend A prev v (List.finRange n)=some path := by
      simpa [cachedBFSStep, cached_vector_get_ofFn, hp] using ho
    obtain ⟨u, _, walkPrefix, hprefix, hedge, hpath⟩ :=
      cached_bfs_extend_some A prev v (List.finRange n) path he
    obtain ⟨hwalk, hlen⟩ := hprev u walkPrefix hprefix
    rw [hpath]
    refine ⟨CachedResidualWalk.extend hwalk hedge, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | some oldpath =>
    have he : oldpath=path := by
      have h : some oldpath=some path := by simpa [cachedBFSStep, cached_vector_get_ofFn, hp] using ho
      exact Option.some.inj h
    subst path
    obtain ⟨hwalk, hlen⟩ := hprev v oldpath hp
    exact ⟨hwalk, by omega⟩

theorem cached_bfs_layers_valid {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ) :
    CachedBFSTableValid A s k (cachedBFSLayers A s k) := by
  induction k with
  | zero => exact cached_bfs_initial_valid A s
  | succ k ih => exact cached_bfs_step_valid A s k (cachedBFSLayers A s k) ih

theorem cached_bfs_path_some_walk {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (path : List (Fin n)) (ho : cachedBFSPath A s t=some path) :
    CachedResidualWalk A s t path ∧ path.length ≤ n+1 :=
  cached_bfs_layers_valid A s n t path ho

/-- The walk predicate records actual source/target labels and every stored edge. -/
theorem cached_residual_walk_endpoints {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (path : List (Fin n)) (hw : CachedResidualWalk A s t path) :
    path.head?=some s ∧ path.getLast?=some t := by
  induction hw with
  | start => simp
  | @extend u v walkPrefix hwalk hedge ih =>
    constructor
    · cases hp : walkPrefix with
      | nil => simp [hp] at ih
      | cons a rest => simpa [hp] using ih.1
    · simp

/-- The program's actual Some payload has the asserted endpoints and n-edge bound. -/
theorem cached_bfs_path_some_endpoints {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (path : List (Fin n)) (ho : cachedBFSPath A s t=some path) :
    path.head?=some s ∧ path.getLast?=some t ∧ path.length ≤ n+1 := by
  obtain ⟨hw, hlen⟩ := cached_bfs_path_some_walk A s t path ho
  obtain ⟨hstart, hend⟩ := cached_residual_walk_endpoints A s t path hw
  exact ⟨hstart, hend, hlen⟩


def cachedBFSAdjFunction {n : ℕ} (A : CachedBFSAdj n) (u v : Fin n) : Bool :=
  (A.get u).get v

theorem cached_bfs_step_none_iff {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) :
    (cachedBFSStep A prev).get v=none ↔ prev.get v=none ∧
      ∀ u, prev.get u=none ∨ (A.get u).get v=false := by
  cases hp : prev.get v with
  | some path => simp [cachedBFSStep, cached_vector_get_ofFn, hp]
  | none =>
    have he := cached_bfs_extend_none_iff A prev v (List.finRange n)
    simpa [cachedBFSStep, cached_vector_get_ofFn, hp] using he

/-- Stored presence is exactly the already-proved functional reach-layer model;
the implementation itself does not evaluate that functional model. -/
theorem cached_bfs_layers_none_iff {n : ℕ} (A : CachedBFSAdj n) (s : Fin n)
    (k : ℕ) (v : Fin n) :
    (cachedBFSLayers A s k).get v=none ↔
      v ∉ residualReachLayers (cachedBFSAdjFunction A) s k := by
  induction k generalizing v with
  | zero => simp [cachedBFSLayers, cachedBFSInitial, cached_vector_get_ofFn, residual_reach_layers_zero]
  | succ k ih =>
    rw [cached_bfs_layers_succ, cached_bfs_step_none_iff, residual_reach_layers_succ]
    constructor
    · rintro ⟨hv, hall⟩ hm
      rcases Finset.mem_union.mp hm with hold | hnew
      · exact (ih v).mp hv hold
      · obtain ⟨_, u, hu, hedge⟩ := Finset.mem_filter.mp hnew
        rcases hall u with hnone | hfalse
        · exact (ih u).mp hnone hu
        · change (A.get u).get v=true at hedge
          rw [hfalse] at hedge
          cases hedge
    · intro hn
      refine ⟨(ih v).mpr (fun hv => hn (Finset.mem_union_left _ hv)), ?_⟩
      intro u
      by_cases hu : u ∈ residualReachLayers (cachedBFSAdjFunction A) s k
      · right
        cases he : (A.get u).get v with
        | false => rfl
        | true =>
          exfalso
          apply hn
          apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, u, hu, he⟩
      · exact Or.inl ((ih u).mpr hu)

theorem cached_bfs_path_none_iff_unreachable {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n) :
    cachedBFSPath A s t=none ↔
      ¬ Relation.ReflTransGen (fun u v => (A.get u).get v=true) s t := by
  exact (cached_bfs_layers_none_iff A s n t).trans
    (not_congr (residual_reach_layers_iff (cachedBFSAdjFunction A) s t))

theorem cached_bfs_step_keep {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) (path : List (Fin n)) (hp : prev.get v=some path) :
    (cachedBFSStep A prev).get v=some path := by
  simp [cachedBFSStep, cached_vector_get_ofFn, hp]

theorem cached_bfs_layers_keep {n : ℕ} (A : CachedBFSAdj n) (s v : Fin n)
    {k l : ℕ} (hkl : k ≤ l) (path : List (Fin n))
    (hp : (cachedBFSLayers A s k).get v=some path) :
    (cachedBFSLayers A s l).get v=some path := by
  induction hkl with
  | refl => exact hp
  | @step l h ih =>
    exact cached_bfs_step_keep A (cachedBFSLayers A s l) v path ih

/-- A genuine finite walk is present by its edge count, without a shortest-path
oracle. This supplies the comparison witness for the shortest-output theorem. -/
theorem cached_walk_reach_layer {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (path : List (Fin n)) (hw : CachedResidualWalk A s t path) :
    t ∈ residualReachLayers (cachedBFSAdjFunction A) s (path.length-1) := by
  induction hw with
  | start => simp [residual_reach_layers_zero]
  | @extend u v walkPrefix hwalk hedge ih =>
    have hnonempty : 0 < walkPrefix.length := by
      have hh := (cached_residual_walk_endpoints A s u walkPrefix hwalk).1
      cases walkPrefix <;> simp_all
    have hlen : (walkPrefix++[v]).length-1=Nat.succ (walkPrefix.length-1) := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hlen, residual_reach_layers_succ]
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, ih, hedge⟩

/-- The returned walk is no longer than any genuine walk with the same endpoints.
Because first-discovery entries are retained, this proves shortest-walk length. -/
theorem cached_bfs_path_shortest {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (path other : List (Fin n)) (ho : cachedBFSPath A s t=some path)
    (hw : CachedResidualWalk A s t other) : path.length ≤ other.length := by
  have hlen := (cached_bfs_path_some_walk A s t path ho).2
  have hother : 0 < other.length := by
    have hh := (cached_residual_walk_endpoints A s t other hw).1
    cases other <;> simp_all
  by_cases hk : other.length-1 ≤ n
  · have hr := cached_walk_reach_layer A s t other hw
    have hn : (cachedBFSLayers A s (other.length-1)).get t ≠ none := by
      intro he
      exact (cached_bfs_layers_none_iff A s (other.length-1) t).mp he hr
    cases he : (cachedBFSLayers A s (other.length-1)).get t with
    | none => exact False.elim (hn he)
    | some first =>
      have hp := cached_bfs_layers_keep A s t hk first he
      have heq : first=path := Option.some.inj (hp.symm.trans ho)
      have hf := (cached_bfs_layers_valid A s (other.length-1) t first he).2
      rw [heq] at hf
      omega
  · omega

/-- Exact predecessor extraction from the actual payload, without another search. -/
theorem cached_penultimate_sound {n : ℕ} (path : List (Fin n)) (u t : Fin n)
    (hlast : path.getLast?=some t) (hprev : path.reverse.tail.head?=some u) :
    ∃ walkPrefix, path=walkPrefix++[u,t] := by
  cases hr : path.reverse with
  | nil => simp [hr] at hprev
  | cons last rest =>
    have ht : last=t := by
      have hh : path.reverse.head?=some t := by simpa only [List.head?_reverse] using hlast
      exact Option.some.inj (by simpa [hr] using hh)
    cases rest with
    | nil => simp [hr] at hprev
    | cons prev tail =>
      have hu : prev=u := Option.some.inj (by simpa [hr] using hprev)
      have he : path=(last::prev::tail).reverse := by rw [← hr, List.reverse_reverse]
      subst last
      subst prev
      refine ⟨tail.reverse, ?_⟩
      rw [he]
      simp [List.reverse_cons, List.append_assoc]

theorem cached_bfs_result_origin {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (path : List (Fin n)) (parent : Option (Fin n))
    (ho : cachedBFSResult A s t=some (path,parent)) :
    cachedBFSPath A s t=some path ∧ parent=path.reverse.tail.head? := by
  cases hp : cachedBFSPath A s t with
  | none => simp [cachedBFSResult, hp] at ho
  | some found =>
    have he : (found, found.reverse.tail.head?)=(path,parent) := by
      exact Option.some.inj (by simpa [cachedBFSResult, hp] using ho)
    have hf : found=path := congrArg Prod.fst he
    subst path
    exact ⟨rfl, (congrArg Prod.snd he).symm⟩

theorem cached_bfs_result_predecessor {n : ℕ} (A : CachedBFSAdj n) (s t u : Fin n)
    (path : List (Fin n)) (ho : cachedBFSResult A s t=some (path,some u)) :
    ∃ walkPrefix, path=walkPrefix++[u,t] := by
  obtain ⟨hp, he⟩ := cached_bfs_result_origin A s t path (some u) ho
  have ht := (cached_bfs_path_some_endpoints A s t path hp).2.1
  exact cached_penultimate_sound path u t ht he.symm

theorem cached_residual_adjacency_coherence {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (u v : Fin n) :
    cachedBFSAdjFunction (cacheResidualAdj C F) u v=rationalResidualAdj C F u v := by
  simp [cachedBFSAdjFunction, cacheResidualAdj, cached_vector_get_ofFn]

theorem cached_rational_residual_none_iff {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (s t : Fin n) :
    cachedRationalResidualPath C F s t=none ↔
      ¬ Relation.ReflTransGen (fun u v => rationalResidualAdj C F u v=true) s t := by
  change (cachedBFSPath (cacheResidualAdj C F) s t).map
    (fun path => (path, path.reverse.tail.head?))=none ↔ _
  rw [Option.map_eq_none_iff]
  have hh := cached_bfs_path_none_iff_unreachable (cacheResidualAdj C F) s t
  change cachedBFSPath (cacheResidualAdj C F) s t=none ↔
    ¬ Relation.ReflTransGen (fun u v =>
      cachedBFSAdjFunction (cacheResidualAdj C F) u v=true) s t at hh
  simpa only [cached_residual_adjacency_coherence] using hh

/-- Reachability is sufficient for an actual shortest Some payload, not an
assumed certificate argument passed into the implementation. -/
theorem cached_bfs_reachable_some {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n)
    (hr : Relation.ReflTransGen (fun u v => (A.get u).get v=true) s t) :
    ∃ path, cachedBFSPath A s t=some path ∧
      CachedResidualWalk A s t path ∧ path.length ≤ n+1 ∧
      ∀ other, CachedResidualWalk A s t other → path.length ≤ other.length := by
  cases ho : cachedBFSPath A s t with
  | none => exact False.elim ((cached_bfs_path_none_iff_unreachable A s t).mp ho hr)
  | some path =>
    obtain ⟨hw, hlen⟩ := cached_bfs_path_some_walk A s t path ho
    exact ⟨path, rfl, hw, hlen, fun other hother =>
      cached_bfs_path_shortest A s t path other ho hother⟩

end SparseCompletion
