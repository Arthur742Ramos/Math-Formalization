/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. The actual cached path earns all finite safety checks;
for distinct endpoints this makes the materialized augmentation attempt complete
for actual rational residual reachability. No flow-feasibility oracle, assumed
successful path or runtime Classical.choice. No iteration or complexity theorem.
-/
module
public import RationalTableAugmentation
public import RationalCachedPathAugmentation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Every check is a consequence of the actual returned cached BFS payload. -/
theorem rational_augment_candidate_of_cached {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (path : List (Fin n))
    (hp : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s t = some path) :
    RationalAugmentCandidate C F s t path := by
  have hw := (cached_bfs_path_some_walk
    (cacheResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s t path hp).1
  obtain ⟨hhead, hend⟩ := cached_residual_walk_endpoints
    (cacheResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s t path hw
  have hnd := cached_bfs_path_nodup
    (cacheResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s t path hp
  refine ⟨hhead, hend, hnd, ?_⟩
  have hpositive := cached_residual_walk_residuals_positive
    (rationalFlowTableEntry C) (rationalFlowTableEntry F) s t path hw
  cases he : path with
  | nil =>
    have hn : (none : Option (Fin n)) = some s := by simpa only [he, List.head?_nil] using hhead
    cases hn
  | cons a tail =>
    have ha : a = s := Option.some.inj (by simpa only [he, List.head?_cons] using hhead)
    subst a
    simpa only [he, rational_walk_residuals_cons, List.tail_cons] using hpositive

/-- A distinct target excludes the zero-edge singleton, so the actually
computed minimum exists and is positive. No cap is inserted into the minimum. -/
theorem rational_augment_bottleneck_of_cached {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t) (path : List (Fin n))
    (hp : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s t = some path) :
    ∃ δ, rationalPathBottleneck (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s path.tail = some δ ∧ 0 < δ := by
  obtain ⟨hhead, hend, _, hpos⟩ := rational_augment_candidate_of_cached C F s t path hp
  have hepath : s :: path.tail = path := by
    cases he : path with
    | nil =>
      have hn : (none : Option (Fin n)) = some s := by simpa only [he, List.head?_nil] using hhead
      cases hn
    | cons a tail =>
      have ha : a = s := Option.some.inj (by simpa only [he, List.head?_cons] using hhead)
      subst a
      rfl
  have hlast : rationalPathEnd s path.tail = t := by
    have he := rational_path_end_getLast s path.tail
    rw [hepath, hend] at he
    exact (Option.some.inj he).symm
  have hnonempty := rational_path_residuals_nonempty (rationalFlowTableEntry C)
    (rationalFlowTableEntry F) s path.tail (by simpa only [hlast] using hst)
  obtain ⟨δ, hδ⟩ := rational_nonempty_minimum_exists
    (rationalPathResiduals (rationalFlowTableEntry C) (rationalFlowTableEntry F) s path.tail)
    hnonempty
  exact ⟨δ, hδ, rational_nonempty_minimum_positive _ δ hδ hpos⟩

/-- No successful check is assumed: all checks and the bottleneck are earned
from the actual path and source/sink distinctness. -/
theorem rational_augment_once_from_cached {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t) (path : List (Fin n))
    (hp : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s t = some path) :
    ∃ out, rationalAugmentOnce C F s t = some out := by
  have hc := rational_augment_candidate_of_cached C F s t path hp
  obtain ⟨δ, hδ, _⟩ := rational_augment_bottleneck_of_cached C F s t hst path hp
  refine ⟨{ path := path, amount := δ, flow := rationalTablePushPath F s path.tail δ }, ?_⟩
  simp only [rationalAugmentOnce, ite_eq_right hst, hp, Option.bind_some,
    ite_eq_left hc, hδ, Option.map_some]

theorem rational_augment_once_some_iff_cached {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t) :
    (∃ out, rationalAugmentOnce C F s t = some out) ↔
      ∃ path, cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F)) s t = some path := by
  constructor
  · rintro ⟨out, ho⟩
    exact ⟨out.path, (rational_augment_once_origin C F s t out ho).2.1⟩
  · rintro ⟨path, hp⟩
    exact rational_augment_once_from_cached C F s t hst path hp

theorem rational_augment_once_none_iff_cached {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t) :
    rationalAugmentOnce C F s t = none ↔
      cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F)) s t = none := by
  constructor
  · intro hn
    cases hp : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F)) s t with
    | none => rfl
    | some path =>
      obtain ⟨out, ho⟩ := rational_augment_once_from_cached C F s t hst path hp
      rw [hn] at ho
      cases ho
  · intro hp
    simp only [rationalAugmentOnce, ite_eq_right hst, hp, Option.bind_none]

/-- This is actual finite residual unreachability, not a supplied certificate.
Distinctness is essential: the source reaches itself reflexively but the
augmentation program intentionally rejects the zero-edge path. -/
theorem rational_augment_once_none_iff_unreachable {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t) :
    rationalAugmentOnce C F s t = none ↔
      ¬ Relation.ReflTransGen
        (fun u v => rationalResidualAdj (rationalFlowTableEntry C)
          (rationalFlowTableEntry F) u v = true) s t := by
  have hm : cachedRationalResidualPath (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s t = none ↔
      cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F)) s t = none := by
    change (cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s t).map
        (fun path => (path, path.reverse.tail.head?)) = none ↔ _
    exact Option.map_eq_none_iff
  exact (rational_augment_once_none_iff_cached C F s t hst).trans
    (hm.symm.trans (cached_rational_residual_none_iff
      (rationalFlowTableEntry C) (rationalFlowTableEntry F) s t))

theorem rational_augment_once_complete {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t)
    (hr : Relation.ReflTransGen
      (fun u v => rationalResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F) u v = true) s t) :
    ∃ out, rationalAugmentOnce C F s t = some out := by
  cases ho : rationalAugmentOnce C F s t with
  | none =>
    exact False.elim (((rational_augment_once_none_iff_unreachable C F s t hst).mp ho) hr)
  | some out => exact ⟨out, rfl⟩

/-- Completion of the executable one-step specification for a genuine bounded
skew net-flow input. This is not a theorem that repeated augmentations terminate. -/
theorem rational_augment_once_complete_sound {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t)
    (hcap : ∀ u v, rationalFlowTableEntry F u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry F u v = -rationalFlowTableEntry F v u)
    (hr : Relation.ReflTransGen
      (fun u v => rationalResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F) u v = true) s t) :
    ∃ out, rationalAugmentOnce C F s t = some out ∧ 0 < out.amount ∧
      (∀ u v, rationalFlowTableEntry out.flow u v = -rationalFlowTableEntry out.flow v u) ∧
      (∀ u v, rationalFlowTableEntry out.flow u v ≤ rationalFlowTableEntry C u v) ∧
      (∀ u, u ≠ s → u ≠ t → (∑ v, rationalFlowTableEntry out.flow u v) =
        ∑ v, rationalFlowTableEntry F u v) ∧
      (∑ v, rationalFlowTableEntry out.flow s v) =
        (∑ v, rationalFlowTableEntry F s v) + out.amount := by
  obtain ⟨out, ho⟩ := rational_augment_once_complete C F s t hst hr
  exact ⟨out, ho, rational_augment_once_sound C F s t out hcap hskew ho⟩

end SparseCompletion
