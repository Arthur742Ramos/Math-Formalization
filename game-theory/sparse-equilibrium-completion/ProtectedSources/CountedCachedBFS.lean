/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCOMPILED writer translation of the actual cached BFS. Kept
separate from checked graph34. Counts designated unit source events only;
compiler operational semantics, array allocation/copy costs and operand-bit
costs remain separate. The original List.rec continuation-building pass is
counted even when an early successful predecessor stops forcing continuations.
-/
module
public import ProtectedSources.FlowComputationCost
@[expose] public section
namespace SparseCompletion

/-- The original source builds a thunk at every list constructor. This pair
separates those eager construction events from the demanded predecessor scan.
The successful append executes the shared appendTR writer. Both reversal
passes count their cons visits, cell constructions, and control cases.
-/
def flowCountBFSExtendBuild {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) (labels : List (Fin n)) :
    (Unit → FlowCounted (Option (List (Fin n)))) × FlowWork :=
  List.rec
    ((fun _ => (none, {adminEvents := 1})), {listEvents := 1, adminEvents := 1})
    (fun u _ ih =>
      ((fun _ =>
        match prev.get u with
        | none =>
          let rest := ih.1 ()
          (rest.1, flowWorkAdd {vectorEvents := 1, adminEvents := 2} rest.2)
        | some path =>
          if (A.get u).get v then
            let appended := flowCountAppend path [v]
            (some appended.1, flowWorkAdd
              {listEvents := 1, vectorEvents := 3, adminEvents := 3} appended.2)
          else
            let rest := ih.1 ()
            (rest.1, flowWorkAdd {vectorEvents := 3, adminEvents := 3} rest.2)),
        flowWorkAdd {listEvents := 1, adminEvents := 1} ih.2)) labels

theorem flow_count_bfs_extend_force_erase {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) (labels : List (Fin n)) :
    ((flowCountBFSExtendBuild A prev v labels).1 ()).1 =
      cachedBFSExtend A prev v labels := by
  induction labels with
  | nil => rfl
  | cons u us ih =>
    cases hp : prev.get u with
    | none => simpa [flowCountBFSExtendBuild, cachedBFSExtend, hp] using ih
    | some path =>
      cases he : (A.get u).get v with
      | false => simpa [flowCountBFSExtendBuild, cachedBFSExtend, hp, he] using ih
      | true =>
        simp [flowCountBFSExtendBuild, cachedBFSExtend, hp, he,
          flow_count_append_erase]

theorem flow_count_bfs_extend_build_total {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) (labels : List (Fin n)) :
    flowWorkTotal (flowCountBFSExtendBuild A prev v labels).2 = 2 * (labels.length + 1) := by
  induction labels with
  | nil => rfl
  | cons u us ih =>
    change flowWorkTotal (flowWorkAdd _ (flowCountBFSExtendBuild A prev v us).2) = _
    rw [flow_work_total_add, ih]
    change 2 + 2 * (us.length + 1) = 2 * (us.length + 1 + 1)
    omega

theorem flow_count_bfs_extend_force_bound {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) (labels : List (Fin n)) (L : ℕ)
    (hlen : ∀ u path, prev.get u = some path → path.length ≤ L) :
    flowWorkTotal ((flowCountBFSExtendBuild A prev v labels).1 ()).2 ≤
      8 * (labels.length + 1) + 6 * L + 4 := by
  induction labels with
  | nil => simp only [flowCountBFSExtendBuild, flowWorkTotal, List.length_nil]; omega
  | cons u us ih =>
    cases hp : prev.get u with
    | none =>
      simp only [flowCountBFSExtendBuild, hp]
      change flowWorkTotal (flowWorkAdd _ ((flowCountBFSExtendBuild A prev v us).1 ()).2) ≤ _
      rw [flow_work_total_add]
      change 3 + flowWorkTotal ((flowCountBFSExtendBuild A prev v us).1 ()).2 ≤ _
      simp only [List.length_cons]
      omega
    | some path =>
      have hpLen := hlen u path hp
      cases he : (A.get u).get v with
      | false =>
        simp [flowCountBFSExtendBuild, hp, he]
        change flowWorkTotal (flowWorkAdd _ ((flowCountBFSExtendBuild A prev v us).1 ()).2) ≤ _
        rw [flow_work_total_add]
        change 6 + flowWorkTotal ((flowCountBFSExtendBuild A prev v us).1 ()).2 ≤ _
        omega
      | true =>
        simp [flowCountBFSExtendBuild, hp, he]
        rw [flow_work_total_add, flow_count_append_total]
        change 7 + (6 * path.length + 2) ≤ _
        omega

def flowCountBFSExtend {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) (labels : List (Fin n)) : FlowCounted (Option (List (Fin n))) :=
  let built := flowCountBFSExtendBuild A prev v labels
  let forced := built.1 ()
  (forced.1, flowWorkAdd built.2 forced.2)

theorem flow_count_bfs_extend_erase {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) (labels : List (Fin n)) :
    (flowCountBFSExtend A prev v labels).1 = cachedBFSExtend A prev v labels :=
  flow_count_bfs_extend_force_erase A prev v labels

theorem flow_count_bfs_extend_bound {n : ℕ} (A : CachedBFSAdj n)
    (prev : CachedBFSPaths n) (v : Fin n) (labels : List (Fin n)) (L : ℕ)
    (hlen : ∀ u path, prev.get u = some path → path.length ≤ L) :
    flowWorkTotal (flowCountBFSExtend A prev v labels).2 ≤
      10 * (labels.length + 1) + 6 * L + 4 := by
  have hbuild := flow_count_bfs_extend_build_total A prev v labels
  have hforce := flow_count_bfs_extend_force_bound A prev v labels L hlen
  change flowWorkTotal (flowWorkAdd _ _) ≤ _
  rw [flow_work_total_add]
  omega

def flowCountBFSCell {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (v : Fin n) : FlowCounted (Option (List (Fin n))) :=
  match prev.get v with
  | some path => (some path, {vectorEvents := 1, adminEvents := 1})
  | none =>
    let labels := flowCountFinRange n
    let scan := flowCountBFSExtend A prev v labels.1
    (scan.1, flowWorkAdd {vectorEvents := 1, adminEvents := 1}
      (flowWorkAdd labels.2 scan.2))

def flowCountBFSStep {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n) :
    FlowCounted (CachedBFSPaths n) :=
  flowCountVectorOfFn (flowCountBFSCell A prev)

theorem flow_count_bfs_step_erase {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n) :
    (flowCountBFSStep A prev).1 = cachedBFSStep A prev := by
  unfold flowCountBFSStep cachedBFSStep
  rw [flow_count_vector_ofFn_erase]
  congr 1
  funext v
  cases hp : prev.get v with
  | none => simp only [flowCountBFSCell, hp, flow_count_bfs_extend_erase, flow_count_finRange_erase]
  | some path => simp only [flowCountBFSCell, hp]

theorem flow_count_bfs_step_bound {n : ℕ} (A : CachedBFSAdj n) (prev : CachedBFSPaths n)
    (L : ℕ) (hlen : ∀ u path, prev.get u = some path → path.length ≤ L) :
    flowWorkTotal (flowCountBFSStep A prev).2 ≤ n * (12 * (n + 1) + 6 * L + 10) + 1 := by
  apply flow_count_vector_ofFn_bound _ (12 * (n + 1) + 6 * L + 6)
  intro v
  cases hp : prev.get v with
  | some path => simp only [flowCountBFSCell, hp, flowWorkTotal]; omega
  | none =>
    have hs := flow_count_bfs_extend_bound A prev v (List.finRange n) L hlen
    simp only [List.length_finRange] at hs
    simp only [flowCountBFSCell, hp]
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd (flowCountFinRange n).2
      (flowCountBFSExtend A prev v (flowCountFinRange n).1).2)) ≤ _
    rw [flow_work_total_add, flow_work_total_add, flow_count_finRange_total,
      flow_count_finRange_erase]
    change 2 + (2 * n + 1 + flowWorkTotal (flowCountBFSExtend A prev v (List.finRange n)).2) ≤ _
    omega

def flowCountBFSInitial {n : ℕ} (s : Fin n) : FlowCounted (CachedBFSPaths n) :=
  flowCountVectorOfFn fun v =>
    (if v = s then some [s] else none,
      {listEvents := if v = s then 1 else 0, adminEvents := 2})

theorem flow_count_bfs_initial_erase {n : ℕ} (s : Fin n) :
    (flowCountBFSInitial s).1 = cachedBFSInitial s :=
  flow_count_vector_ofFn_erase _

theorem flow_count_bfs_initial_bound {n : ℕ} (s : Fin n) :
    flowWorkTotal (flowCountBFSInitial s).2 ≤ 7 * n + 1 := by
  calc
    _ ≤ n * (3 + 4) + 1 := flow_count_vector_ofFn_bound _ 3 (by
      intro v
      by_cases he : v = s <;> simp [he, flowWorkTotal])
    _ = 7 * n + 1 := by omega

def flowCountBFSLayers {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) :
    ℕ → FlowCounted (CachedBFSPaths n)
  | 0 =>
    let initial := flowCountBFSInitial s
    (initial.1, flowWorkAdd {adminEvents := 1} initial.2)
  | k + 1 =>
    let prev := flowCountBFSLayers A s k
    let next := flowCountBFSStep A prev.1
    (next.1, flowWorkAdd prev.2 (flowWorkAdd {adminEvents := 1} next.2))

theorem flow_count_bfs_layers_erase {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ) :
    (flowCountBFSLayers A s k).1 = cachedBFSLayers A s k := by
  induction k with
  | zero => exact flow_count_bfs_initial_erase s
  | succ k ih =>
    change (flowCountBFSStep A (flowCountBFSLayers A s k).1).1 = _
    rw [flow_count_bfs_step_erase, ih]
    rfl

theorem flow_count_bfs_layers_bound {n : ℕ} (A : CachedBFSAdj n) (s : Fin n) (k : ℕ) :
    flowWorkTotal (flowCountBFSLayers A s k).2 ≤
      7 * n + 2 + k * (n * (12 * (n + 1) + 6 * (k + 1) + 10) + 2) := by
  induction k with
  | zero =>
    have hi := flow_count_bfs_initial_bound s
    change flowWorkTotal (flowWorkAdd _ _) ≤ _
    rw [flow_work_total_add]
    change 1 + flowWorkTotal (flowCountBFSInitial s).2 ≤ _
    omega
  | succ k ih =>
    have hlen : ∀ u path, (flowCountBFSLayers A s k).1.get u = some path →
        path.length ≤ k + 1 := by
      intro u path ho
      rw [flow_count_bfs_layers_erase] at ho
      exact (cached_bfs_layers_valid A s k u path ho).2
    have hs := flow_count_bfs_step_bound A (flowCountBFSLayers A s k).1 (k + 1) hlen
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
    rw [flow_work_total_add, flow_work_total_add]
    change flowWorkTotal (flowCountBFSLayers A s k).2 +
      (1 + flowWorkTotal (flowCountBFSStep A (flowCountBFSLayers A s k).1).2) ≤ _
    nlinarith [Nat.zero_le (n * k)]

def flowCountBFSPath {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n) :
    FlowCounted (Option (List (Fin n))) :=
  let layers := flowCountBFSLayers A s n
  (layers.1.get t, flowWorkAdd layers.2 {vectorEvents := 1, adminEvents := 1})

theorem flow_count_bfs_path_erase {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n) :
    (flowCountBFSPath A s t).1 = cachedBFSPath A s t := by
  change (flowCountBFSLayers A s n).1.get t = _
  rw [flow_count_bfs_layers_erase]
  rfl

theorem flow_count_bfs_path_bound {n : ℕ} (A : CachedBFSAdj n) (s t : Fin n) :
    flowWorkTotal (flowCountBFSPath A s t).2 ≤ 64 * (n + 1) ^ 3 := by
  have hl := flow_count_bfs_layers_bound A s n
  change flowWorkTotal (flowWorkAdd _ _) ≤ _
  rw [flow_work_total_add]
  change flowWorkTotal (flowCountBFSLayers A s n).2 + 2 ≤ _
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

end SparseCompletion
