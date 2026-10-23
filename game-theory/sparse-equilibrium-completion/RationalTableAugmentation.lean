/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Actual cached residual search, finite candidate checks,
attained positive bottleneck, and materialized rational flow-table update.
This is one augmentation attempt, not a terminating max-flow finder. None is
not yet asserted to mean no augmenting path: safety-check completeness remains
a separate proof obligation. No arithmetic, access, allocation or bit-cost bound.
-/
module
public import RationalPathAugmentation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev RationalFlowTable (n : ℕ) := Vector (Vector ℚ n) n

def rationalFlowTableEntry {n : ℕ} (F : RationalFlowTable n) (u v : Fin n) : ℚ :=
  (F.get u).get v

/-- Evaluate every new entry against the same materialized input table. This is
not a function-valued chain of unevaluated prior flow updates. -/
def rationalTablePushEdge {n : ℕ} (F : RationalFlowTable n)
    (a b : Fin n) (δ : ℚ) : RationalFlowTable n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    rationalNetPushEdge (rationalFlowTableEntry F) a b δ u v

/-- Tail table is computed once as an argument to the next materializing edge
update. Administrative traversal and finite-vector access are not free cost
claims; this definition establishes only actual finite table construction. -/
def rationalTablePushPath {n : ℕ} (F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) : RationalFlowTable n :=
  List.rec (motive := fun _ => Fin n → RationalFlowTable n)
    (fun _ => F) (fun b _ ih start => rationalTablePushEdge (ih b) start b δ) tail a

theorem rational_table_push_edge_entry {n : ℕ} (F : RationalFlowTable n)
    (a b : Fin n) (δ : ℚ) (u v : Fin n) :
    rationalFlowTableEntry (rationalTablePushEdge F a b δ) u v =
      rationalNetPushEdge (rationalFlowTableEntry F) a b δ u v := by
  simp only [rationalFlowTableEntry, rationalTablePushEdge, cached_vector_get_ofFn]

theorem rational_table_push_path_entry {n : ℕ} (F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) (u v : Fin n) :
    rationalFlowTableEntry (rationalTablePushPath F a tail δ) u v =
      rationalNetPushPath (rationalFlowTableEntry F) a tail δ u v := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    change rationalFlowTableEntry
      (rationalTablePushEdge (rationalTablePushPath F b tail δ) a b δ) u v = _
    rw [rational_table_push_edge_entry, rational_net_push_path_cons]
    simp only [rationalNetPushEdge, ih b]

/-- These are actual executable finite checks, not witness inputs. Cached BFS
is already correct; the extra checks make this first wrapper's local soundness
independent of the remaining walk-to-consecutive-residual proof. -/
def RationalAugmentCandidate {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (path : List (Fin n)) : Prop :=
  path.head? = some s ∧ path.getLast? = some t ∧ path.Nodup ∧
    ∀ z ∈ rationalPathResiduals (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s path.tail, 0 < z

instance rationalAugmentCandidateDecidable {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (path : List (Fin n)) :
    Decidable (RationalAugmentCandidate C F s t path) := by
  unfold RationalAugmentCandidate
  infer_instance

structure RationalAugmentResult (n : ℕ) where
  path : List (Fin n)
  amount : ℚ
  flow : RationalFlowTable n

/-- A path found by the actual cached BFS is checked, its actual minimum is
computed, and its edge updates are materialized. Public Option combinators avoid
fresh pattern-match helper identities. Source-equals-target returns None because
zero-edge paths have no positive augmentation bottleneck. -/
def rationalAugmentOnce {n : ℕ} (C F : RationalFlowTable n) (s t : Fin n) :
    Option (RationalAugmentResult n) :=
  if s = t then none else
    let A := cacheResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)
    (cachedBFSPath A s t).bind fun path =>
      if RationalAugmentCandidate C F s t path then
        (rationalPathBottleneck (rationalFlowTableEntry C)
          (rationalFlowTableEntry F) s path.tail).map fun δ =>
          { path := path, amount := δ, flow := rationalTablePushPath F s path.tail δ }
      else none

theorem rational_augment_once_origin {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (ho : rationalAugmentOnce C F s t = some out) :
    s ≠ t ∧
    cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
      (rationalFlowTableEntry F)) s t = some out.path ∧
    RationalAugmentCandidate C F s t out.path ∧
    rationalPathBottleneck (rationalFlowTableEntry C)
      (rationalFlowTableEntry F) s out.path.tail = some out.amount ∧
    out.flow = rationalTablePushPath F s out.path.tail out.amount := by
  by_cases hst : s = t
  · simp only [rationalAugmentOnce, ite_eq_left hst] at ho
    cases ho
  · cases hp : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F)) s t with
    | none =>
      simp only [rationalAugmentOnce, ite_eq_right hst, hp, Option.bind_none] at ho
      cases ho
    | some path =>
      by_cases hv : RationalAugmentCandidate C F s t path
      · cases hm : rationalPathBottleneck (rationalFlowTableEntry C)
          (rationalFlowTableEntry F) s path.tail with
        | none =>
          simp only [rationalAugmentOnce, ite_eq_right hst, hp, Option.bind_some,
            ite_eq_left hv, hm, Option.map_none] at ho
          cases ho
        | some δ =>
          have he : ({ path := path, amount := δ, flow := rationalTablePushPath F s path.tail δ } : RationalAugmentResult n) = out := by
            exact Option.some.inj (by simpa only [rationalAugmentOnce, ite_eq_right hst,
              hp, Option.bind_some, ite_eq_left hv, hm, Option.map_some] using ho)
          subst out
          exact ⟨hst, rfl, hv, hm, rfl⟩
      · simp only [rationalAugmentOnce, ite_eq_right hst, hp, Option.bind_some, ite_eq_right hv] at ho
        cases ho

/-- Local soundness is earned by the actual return value. In particular the
source divergence increases strictly; this does not assert eventual saturation
or an upper bound on the number of successful attempts. -/
theorem rational_augment_once_sound {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (out : RationalAugmentResult n)
    (hcap : ∀ u v, rationalFlowTableEntry F u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry F u v = -rationalFlowTableEntry F v u)
    (ho : rationalAugmentOnce C F s t = some out) :
    0 < out.amount ∧
    (∀ u v, rationalFlowTableEntry out.flow u v = -rationalFlowTableEntry out.flow v u) ∧
    (∀ u v, rationalFlowTableEntry out.flow u v ≤ rationalFlowTableEntry C u v) ∧
    (∀ u, u ≠ s → u ≠ t → (∑ v, rationalFlowTableEntry out.flow u v) =
      ∑ v, rationalFlowTableEntry F u v) ∧
    (∑ v, rationalFlowTableEntry out.flow s v) =
      (∑ v, rationalFlowTableEntry F s v) + out.amount := by
  obtain ⟨hst, _, hcand, hm, hflow⟩ := rational_augment_once_origin C F s t out ho
  obtain ⟨hhead, hend, hnd, hpos⟩ := hcand
  have hepath : s :: out.path.tail = out.path := by
    cases hp : out.path with
    | nil => simp only [hp, List.head?_nil] at hhead; cases hhead
    | cons a tail =>
      have ha : a = s := Option.some.inj (by simpa only [hp, List.head?_cons] using hhead)
      subst a
      rfl
  have hlast : rationalPathEnd s out.path.tail = t := by
    have h := rational_path_end_getLast s out.path.tail
    rw [hepath, hend] at h
    exact (Option.some.inj h).symm
  have hsimple : (s :: out.path.tail).Nodup := by simpa only [hepath] using hnd
  obtain ⟨hδ, hsk, hca, hcons⟩ := rational_path_bottleneck_augmentation
    (rationalFlowTableEntry C) (rationalFlowTableEntry F) hcap hskew s
    out.path.tail hsimple out.amount hm hpos
  have hentry : ∀ u v, rationalFlowTableEntry out.flow u v =
      rationalNetPushPath (rationalFlowTableEntry F) s out.path.tail out.amount u v := by
    intro u v
    rw [hflow, rational_table_push_path_entry]
  refine ⟨hδ, ?_, ?_, ?_, ?_⟩
  · intro u v
    simpa only [hentry] using hsk u v
  · intro u v
    simpa only [hentry] using hca u v
  · intro u hus hut
    simpa only [hentry] using hcons u hus (by simpa only [hlast] using hut)
  · simpa only [hentry] using rational_net_push_path_source_value
      (rationalFlowTableEntry F) s out.path.tail out.amount
      (by simpa only [hlast] using hst)

end SparseCompletion
