/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCHECKED. Capacity-independent bound on the number of actual
successful cached-shortest-path augmentations. The proof charges each real
bottleneck saturation to its oriented capacity-support arc and BFS level.
No bound on rational arithmetic or machine/bit runtime is asserted.
-/
module
public import RationalCriticalArc
@[expose] public section
namespace SparseCompletion

/-- Fixed oriented support of the capacity table. For nonnegative capacities
this is precisely the symmetric closure of its positive directed entries. -/
def rationalCapacityArcSupport {n : ℕ} (C : RationalFlowTable n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e =>
    0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1

theorem rational_successful_trace_feasible {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (k : ℕ) (F : ℕ → RationalFlowTable n)
    (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (hcap : ∀ u v, rationalFlowTableEntry (F 0) u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry (F 0) u v =
      -rationalFlowTableEntry (F 0) v u) (i : ℕ) (hik : i ≤ k) :
    (∀ u v, rationalFlowTableEntry (F i) u v ≤ rationalFlowTableEntry C u v) ∧
    (∀ u v, rationalFlowTableEntry (F i) u v =
      -rationalFlowTableEntry (F i) v u) := by
  revert hik
  induction i with
  | zero => intro _; exact ⟨hcap, hskew⟩
  | succ i ih =>
    intro hik
    have hi : i < k := by omega
    obtain ⟨hc, hs⟩ := ih (by omega)
    obtain ⟨_, hs', hc', _, _⟩ := rational_augment_once_sound C (F i) s t (out i)
      hc hs (hreturn i hi)
    rw [hnext i hi]
    exact ⟨hc', hs'⟩

theorem rational_augment_once_edge_in_capacity_support {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (out : RationalAugmentResult n)
    (hcap : ∀ u v, rationalFlowTableEntry F u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry F u v = -rationalFlowTableEntry F v u)
    (ho : rationalAugmentOnce C F s t = some out)
    (u v : Fin n) (he : (u, v) ∈ rationalWalkEdges out.path) :
    (u, v) ∈ rationalCapacityArcSupport C := by
  have hres := rational_augment_once_edge_residual C F s t out ho u v he
  have hr := hcap v u
  have hs := hskew u v
  simp only [rationalCapacityArcSupport, Finset.mem_filter, Finset.mem_univ,
    true_and]
  linarith

/-- A genuine finite successful execution has at most (V+2)E augmentations,
where E is the fixed number of oriented capacity-support arcs. The injection
labels each executed augmentation by an attained critical arc and its actual
cached BFS tail level. Repeating the same arc forces a level increase by two.
The harmless +2 uses the existing finite unreachable-sentinel bound uniformly.
-/
theorem rational_successful_trace_length_bound {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (k : ℕ) (F : ℕ → RationalFlowTable n)
    (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (hcap : ∀ u v, rationalFlowTableEntry (F 0) u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry (F 0) u v =
      -rationalFlowTableEntry (F 0) v u) :
    k ≤ (rationalCapacityArcSupport C).card * (n + 2) := by
  classical
  choose u v hedge hsat using fun i : Fin k =>
    rational_augment_once_critical_arc C (F i.val) s t (out i.val)
      (hreturn i.val i.isLt)
  have hsupp : ∀ i : Fin k, (u i, v i) ∈ rationalCapacityArcSupport C := by
    intro i
    obtain ⟨hc, hs⟩ := rational_successful_trace_feasible C s t k F out hreturn hnext
      hcap hskew i.val (le_of_lt i.isLt)
    exact rational_augment_once_edge_in_capacity_support C (F i.val) s t (out i.val)
      hc hs (hreturn i.val i.isLt) (u i) (v i) (hedge i)
  let key : Fin k → ({e // e ∈ rationalCapacityArcSupport C} × Fin (n + 2)) :=
    fun i => (⟨(u i, v i), hsupp i⟩,
      ⟨cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (F i.val))) s (u i), by
        have hb := cached_bfs_distance_bound
          (cacheResidualAdj (rationalFlowTableEntry C)
            (rationalFlowTableEntry (F i.val))) s (u i)
        omega⟩)
  have hinj : Function.Injective key := by
    intro a b heq
    have hp : (u a, v a) = (u b, v b) := congrArg (fun x => x.1.val) heq
    have hu : u a = u b := congrArg Prod.fst hp
    have hv : v a = v b := congrArg Prod.snd hp
    have hd : cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (F a.val))) s (u a) =
      cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (F b.val))) s (u b) :=
      congrArg (fun x => x.2.val) heq
    by_contra hn
    have hne : a.val ≠ b.val := fun he => hn (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hlater : (u a, v a) ∈ rationalWalkEdges (out b.val).path := by
        simpa only [hu, hv] using hedge b
      have hgap := rational_successful_trace_critical_recurrence C s t k F out
        hreturn hnext a.val b.val hab b.isLt (u a) (v a) (hedge a) (hsat a) hlater
      rw [hu] at hd hgap
      omega
    · have hlater : (u b, v b) ∈ rationalWalkEdges (out a.val).path := by
        simpa only [hu, hv] using hedge a
      have hgap := rational_successful_trace_critical_recurrence C s t k F out
        hreturn hnext b.val a.val hba a.isLt (u b) (v b) (hedge b) (hsat b) hlater
      rw [hu] at hd
      omega
  have hcard := Fintype.card_le_of_injective key hinj
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe] using hcard

/-- Explicit constant form of the O(VE) actual-augmentation bound. A source
vertex already forces V positive. -/
theorem rational_successful_trace_length_le_three_mul_vertices_edges {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (k : ℕ)
    (F : ℕ → RationalFlowTable n) (out : ℕ → RationalAugmentResult n)
    (hreturn : ∀ i, i < k → rationalAugmentOnce C (F i) s t = some (out i))
    (hnext : ∀ i, i < k → F (i + 1) = (out i).flow)
    (hcap : ∀ u v, rationalFlowTableEntry (F 0) u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry (F 0) u v =
      -rationalFlowTableEntry (F 0) v u) :
    k ≤ 3 * n * (rationalCapacityArcSupport C).card := by
  have hb := rational_successful_trace_length_bound C s t k F out hreturn hnext hcap hskew
  have hn : 0 < n := by have hs := s.isLt; omega
  nlinarith

end SparseCompletion
