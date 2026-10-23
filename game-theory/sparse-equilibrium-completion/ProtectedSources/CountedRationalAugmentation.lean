/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCOMPILED. Executable writer translation of rationalAugmentOnce,
including the actual BFS, complete candidate decision, a second residual-list
construction for the bottleneck, and every materialized path/table update.
The count is a designated source-event model, not a machine/bit-runtime claim.
-/
module
public import ProtectedSources.CountedAugmentCandidate
@[expose] public section
namespace SparseCompletion

def flowCountAugmentOnce {n : ℕ} (C F : RationalFlowTable n) (s t : Fin n) :
    FlowCounted (Option (RationalAugmentResult n)) :=
  if s = t then (none, {adminEvents := 2}) else
    let cache := flowCountResidualCache C F
    let bfs := flowCountBFSPath cache.1 s t
    match bfs.1 with
    | none =>
      (none, flowWorkAdd cache.2 (flowWorkAdd bfs.2 {adminEvents := 3}))
    | some path =>
      let candidate := flowCountAugmentCandidate C F s t path
      if candidate.1 then
        let amount := flowCountPathBottleneck C F s path.tail
        match amount.1 with
        | none =>
          (none, flowWorkAdd cache.2 (flowWorkAdd bfs.2
            (flowWorkAdd candidate.2 (flowWorkAdd amount.2 {adminEvents := 5}))))
        | some δ =>
          let pushed := flowCountTablePushPath F s path.tail δ
          (some {path := path, amount := δ, flow := pushed.1},
            flowWorkAdd cache.2 (flowWorkAdd bfs.2 (flowWorkAdd candidate.2
              (flowWorkAdd amount.2 (flowWorkAdd pushed.2 {adminEvents := 7})))))
      else
        (none, flowWorkAdd cache.2 (flowWorkAdd bfs.2
          (flowWorkAdd candidate.2 {adminEvents := 4})))

theorem flow_count_augment_once_erase {n : ℕ} (C F : RationalFlowTable n) (s t : Fin n) :
    (flowCountAugmentOnce C F s t).1 = rationalAugmentOnce C F s t := by
  by_cases hst : s = t
  · simp [flowCountAugmentOnce, rationalAugmentOnce, hst]
  · cases hp : cachedBFSPath (cacheResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry F)) s t with
    | none =>
      simp [flowCountAugmentOnce, rationalAugmentOnce, hst, flow_count_residual_cache_erase,
        flow_count_bfs_path_erase, hp]
    | some path =>
      by_cases hc : RationalAugmentCandidate C F s t path
      · cases hm : rationalPathBottleneck (rationalFlowTableEntry C)
          (rationalFlowTableEntry F) s path.tail with
        | none =>
          simp [flowCountAugmentOnce, rationalAugmentOnce, hst, flow_count_residual_cache_erase,
            flow_count_bfs_path_erase, hp, flow_count_augment_candidate_erase, hc,
            flow_count_path_bottleneck_erase, hm]
        | some δ =>
          simp [flowCountAugmentOnce, rationalAugmentOnce, hst, flow_count_residual_cache_erase,
            flow_count_bfs_path_erase, hp, flow_count_augment_candidate_erase, hc,
            flow_count_path_bottleneck_erase, hm, flow_count_table_push_path_erase]
      · simp [flowCountAugmentOnce, rationalAugmentOnce, hst, flow_count_residual_cache_erase,
          flow_count_bfs_path_erase, hp, flow_count_augment_candidate_erase, hc]

theorem flow_count_augment_once_bound {n : ℕ} (C F : RationalFlowTable n) (s t : Fin n) :
    flowWorkTotal (flowCountAugmentOnce C F s t).2 ≤ 1000 * (n + 2) ^ 3 := by
  have hc := flow_count_residual_cache_bound C F
  have hb := flow_count_bfs_path_bound (flowCountResidualCache C F).1 s t
  by_cases hst : s = t
  · simp only [flowCountAugmentOnce, hst, ↓reduceIte]
    change 2 ≤ 1000 * (n + 2) ^ 3
    nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]
  · cases hp : (flowCountBFSPath (flowCountResidualCache C F).1 s t).1 with
    | none =>
      simp only [flowCountAugmentOnce, hst, ↓reduceIte, hp]
      repeat rw [flow_work_total_add]
      change flowWorkTotal (flowCountResidualCache C F).2 +
        (flowWorkTotal (flowCountBFSPath (flowCountResidualCache C F).1 s t).2 + 3) ≤ _
      nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]
    | some path =>
      have hlen : path.length ≤ n + 1 := by
        rw [flow_count_bfs_path_erase] at hp
        exact (cached_bfs_path_some_walk _ s t path hp).2
      have htail : path.tail.length ≤ n + 1 := by
        have ht : path.tail.length ≤ path.length := by cases path <;> simp
        omega
      have hcan := flow_count_augment_candidate_bound C F s t path
      have hcan' : flowWorkTotal (flowCountAugmentCandidate C F s t path).2 ≤
          32 * (n + 2) ^ 2 := by
        apply le_trans hcan
        have hl : path.length + 1 ≤ n + 2 := by omega
        exact Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hl 2)
      cases hv : (flowCountAugmentCandidate C F s t path).1 with
      | false =>
        simp only [flowCountAugmentOnce, hst, ↓reduceIte, hp, hv, Bool.false_eq_true]
        repeat rw [flow_work_total_add]
        change flowWorkTotal (flowCountResidualCache C F).2 +
          (flowWorkTotal (flowCountBFSPath (flowCountResidualCache C F).1 s t).2 +
            (flowWorkTotal (flowCountAugmentCandidate C F s t path).2 + 4)) ≤ _
        nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]
      | true =>
        have hm := flow_count_path_bottleneck_bound C F s path.tail
        have hm' : flowWorkTotal (flowCountPathBottleneck C F s path.tail).2 ≤
            13 * (n + 1) + 4 := by omega
        cases hd : (flowCountPathBottleneck C F s path.tail).1 with
        | none =>
          simp only [flowCountAugmentOnce, hst, ↓reduceIte, hp, hv, hd]
          repeat rw [flow_work_total_add]
          change flowWorkTotal (flowCountResidualCache C F).2 +
            (flowWorkTotal (flowCountBFSPath (flowCountResidualCache C F).1 s t).2 +
              (flowWorkTotal (flowCountAugmentCandidate C F s t path).2 + (flowWorkTotal (flowCountPathBottleneck C F s path.tail).2 + 5))) ≤ _
          nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]
        | some δ =>
          have hpush := flow_count_table_push_path_bound F s path.tail δ
          have hpush' : flowWorkTotal (flowCountTablePushPath F s path.tail δ).2 ≤
              (n + 1) * (24 * (n + 1) ^ 2 + 3) + 2 := by
            apply le_trans hpush
            exact Nat.add_le_add_right (Nat.mul_le_mul_right _ htail) 2
          simp only [flowCountAugmentOnce, hst, ↓reduceIte, hp, hv, hd]
          repeat rw [flow_work_total_add]
          change flowWorkTotal (flowCountResidualCache C F).2 +
            (flowWorkTotal (flowCountBFSPath (flowCountResidualCache C F).1 s t).2 +
              (flowWorkTotal (flowCountAugmentCandidate C F s t path).2 + (flowWorkTotal (flowCountPathBottleneck C F s path.tail).2 +
                (flowWorkTotal (flowCountTablePushPath F s path.tail δ).2 + 7)))) ≤ _
          nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

/-- Same demanded recursion as the actual direct loop; an unsuccessful return
never constructs or invokes the remaining-fuel continuation. -/
def flowCountTableFlowDirect {n : ℕ} (C : RationalFlowTable n) (s t : Fin n) :
    ℕ → RationalFlowTable n → FlowCounted (RationalFlowTable n)
  | 0, F => (F, {adminEvents := 1})
  | fuel + 1, F =>
    let attempt := flowCountAugmentOnce C F s t
    match attempt.1 with
    | none => (F, flowWorkAdd attempt.2 {adminEvents := 2})
    | some out =>
      let rest := flowCountTableFlowDirect C s t fuel out.flow
      (rest.1, flowWorkAdd attempt.2 (flowWorkAdd {adminEvents := 2} rest.2))

theorem flow_count_table_flow_direct_erase {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (fuel : ℕ) (F : RationalFlowTable n) :
    (flowCountTableFlowDirect C s t fuel F).1 = rationalTableFlowIterateDirect C s t fuel F := by
  induction fuel generalizing F with
  | zero => rfl
  | succ fuel ih =>
    cases ho : rationalAugmentOnce C F s t with
    | none =>
      simp [flowCountTableFlowDirect, flow_count_augment_once_erase, ho,
        rational_table_flow_iterate_direct_of_none C F s t (fuel + 1) ho]
    | some out =>
      simp only [flowCountTableFlowDirect, flow_count_augment_once_erase, ho]
      rw [ih out.flow]
      change _ = Option.rec (motive := fun _ => RationalFlowTable n) F
        (fun result => rationalTableFlowIterateDirect C s t fuel result.flow)
        (rationalAugmentOnce C F s t)
      rw [ho]

theorem flow_count_table_flow_direct_bound {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (fuel : ℕ) (F : RationalFlowTable n) :
    flowWorkTotal (flowCountTableFlowDirect C s t fuel F).2 ≤
      (fuel + 1) * (1000 * (n + 2) ^ 3 + 2) := by
  induction fuel generalizing F with
  | zero =>
    change 1 ≤ (0 + 1) * (1000 * (n + 2) ^ 3 + 2)
    omega
  | succ fuel ih =>
    have ha := flow_count_augment_once_bound C F s t
    cases ho : (flowCountAugmentOnce C F s t).1 with
    | none =>
      simp only [flowCountTableFlowDirect, ho]
      rw [flow_work_total_add]
      change flowWorkTotal (flowCountAugmentOnce C F s t).2 + 2 ≤ _
      nlinarith
    | some out =>
      have ht := ih out.flow
      simp only [flowCountTableFlowDirect, ho]
      rw [flow_work_total_add, flow_work_total_add]
      change flowWorkTotal (flowCountAugmentOnce C F s t).2 +
        (2 + flowWorkTotal (flowCountTableFlowDirect C s t fuel out.flow).2) ≤ _
      nlinarith

theorem rational_capacity_arc_support_card_le {n : ℕ} (C : RationalFlowTable n) :
    (rationalCapacityArcSupport C).card ≤ n * n := by
  have hcard := Finset.card_le_card
    (Finset.filter_subset (fun e : Fin n × Fin n =>
      0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1) Finset.univ)
  simpa only [rationalCapacityArcSupport, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin] using hcard

/-- Counter bound for running the actual graph-fuel loop after its fuel and
initial table have been computed. Pricing construction of the Finset support,
its cardinal, and the zero table is a distinct initialization obligation.
This boundary is explicit: this theorem is not total finder runtime. -/
theorem flow_count_graph_fuel_loop_bound {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) :
    flowWorkTotal (flowCountTableFlowDirect C s t (rationalTableGraphFuel C) F).2 ≤
      2000 * (n + 2) ^ 6 := by
  have he := rational_capacity_arc_support_card_le C
  have hf : rationalTableGraphFuel C + 1 ≤ (n + 2) ^ 3 := by
    unfold rationalTableGraphFuel
    nlinarith [Nat.mul_le_mul_right (n + 2) he, Nat.zero_le (n ^ 3)]
  have ht := flow_count_table_flow_direct_bound C s t (rationalTableGraphFuel C) F
  have hm := Nat.mul_le_mul_right (1000 * (n + 2) ^ 3 + 2) hf
  apply le_trans ht
  apply le_trans hm
  nlinarith [Nat.zero_le ((n + 2) ^ 3), Nat.zero_le ((n + 2) ^ 6)]

end SparseCompletion
