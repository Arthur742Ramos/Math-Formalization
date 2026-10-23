/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCOMPILED. Real finder initialization: canonical Fin.univ product,
Multiset map/join representation, filtered oriented support, actual cardinal,
natural fuel arithmetic, and materialized zero table. Erasure is to the actual
graph-fuel finder, not an alternative denominator-fuel recomputation.

The collection adapter counts source list primitives after pinned map/filter/
append TR replacements. Join charges its actual foldrTR conversion/array pass
per input row as well as each append; those independent pure conversion events
are batched with the corresponding fold event. Array allocation/copy machine
time, rational operand bits and compiler instruction counts remain unpriced.
-/
module
public import ProtectedSources.CountedRationalAugmentation
@[expose] public section
namespace SparseCompletion

def flowCountMap {α β : Type*} (f : α → FlowCounted β) (xs : List α) :
    FlowCounted (List β) := go xs []
where
  go : List α → List β → FlowCounted (List β)
    | [], acc =>
      let rev := flowCountReverseAux acc []
      (rev.1, flowWorkAdd {adminEvents := 1} rev.2)
    | a :: tail, acc =>
      let head := f a
      let rest := go tail (head.1 :: acc)
      (rest.1, flowWorkAdd head.2
        (flowWorkAdd {listEvents := 2, adminEvents := 1} rest.2))

theorem flow_count_map_go_erase {α β : Type*} (f : α → FlowCounted β)
    (xs : List α) (acc : List β) :
    (flowCountMap.go f xs acc).1 = List.mapTR.loop (fun a => (f a).1) xs acc := by
  induction xs generalizing acc with
  | nil => exact flow_count_reverse_aux_erase acc []
  | cons a xs ih => exact ih ((f a).1 :: acc)

theorem flow_count_map_erase {α β : Type*} (f : α → FlowCounted β) (xs : List α) :
    (flowCountMap f xs).1 = xs.map (fun a => (f a).1) := by
  rw [List.map_eq_mapTR]
  exact flow_count_map_go_erase f xs []

theorem flow_count_map_go_bound {α β : Type*} (f : α → FlowCounted β)
    (B : ℕ) (hb : ∀ a, flowWorkTotal (f a).2 ≤ B) (xs : List α) (acc : List β) :
    flowWorkTotal (flowCountMap.go f xs acc).2 ≤
      xs.length * (B + 6) + 3 * acc.length + 2 := by
  induction xs generalizing acc with
  | nil =>
    have hr := flow_count_reverse_aux_total acc []
    change flowWorkTotal (flowWorkAdd _ (flowCountReverseAux acc []).2) ≤ _
    rw [flow_work_total_add, hr]
    change 1 + (3 * acc.length + 1) ≤ _
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    omega
  | cons a xs ih =>
    have hh := hb a
    have ht := ih ((f a).1 :: acc)
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
    rw [flow_work_total_add, flow_work_total_add]
    change flowWorkTotal (f a).2 + (3 + flowWorkTotal (flowCountMap.go f xs ((f a).1 :: acc)).2) ≤ _
    simp only [List.length_cons] at ht ⊢
    nlinarith

theorem flow_count_map_bound {α β : Type*} (f : α → FlowCounted β)
    (B : ℕ) (hb : ∀ a, flowWorkTotal (f a).2 ≤ B) (xs : List α) :
    flowWorkTotal (flowCountMap f xs).2 ≤ xs.length * (B + 6) + 2 := by
  simpa only [flowCountMap, List.length_nil, mul_zero, add_zero] using
    flow_count_map_go_bound f B hb xs []

def flowCountJoin {α : Type*} : List (List α) → FlowCounted (List α)
  | [] => ([], {adminEvents := 2})
  | row :: rows =>
    let rest := flowCountJoin rows
    let joined := flowCountAppend row rest.1
    (joined.1, flowWorkAdd rest.2
      (flowWorkAdd {listEvents := 1, vectorEvents := 2, adminEvents := 3} joined.2))

theorem flow_count_join_erase {α : Type*} (rows : List (List α)) :
    (flowCountJoin rows).1 = rows.flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change (flowCountAppend _ _).1 = _
    rw [flow_count_append_erase, ih]
    rfl

theorem flow_count_join_bound {α : Type*} (rows : List (List α)) (L : ℕ)
    (hlen : ∀ row ∈ rows, row.length ≤ L) :
    flowWorkTotal (flowCountJoin rows).2 ≤ rows.length * (6 * L + 8) + 2 := by
  induction rows with
  | nil => simp [flowCountJoin, flowWorkTotal]
  | cons row rows ih =>
    have hr := hlen row List.mem_cons_self
    have ht := ih (fun a ha => hlen a (List.mem_cons_of_mem row ha))
    have ha := flow_count_append_total row (flowCountJoin rows).1
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
    rw [flow_work_total_add, flow_work_total_add]
    change flowWorkTotal (flowCountJoin rows).2 + (6 + flowWorkTotal (flowCountAppend row (flowCountJoin rows).1).2) ≤ _
    simp only [List.length_cons]
    nlinarith

def flowCountPairUniverse (n : ℕ) : FlowCounted (List (Fin n × Fin n)) :=
  let left := flowCountFinRange n
  let right := flowCountFinRange n
  let rows := flowCountMap
    (fun a => flowCountMap (fun b => ((a, b), {adminEvents := 1})) right.1) left.1
  let joined := flowCountJoin rows.1
  (joined.1, flowWorkAdd left.2 (flowWorkAdd right.2 (flowWorkAdd rows.2 joined.2)))

theorem flow_count_pair_universe_erase (n : ℕ) :
    (flowCountPairUniverse n).1 =
      (List.finRange n).flatMap (fun a => (List.finRange n).map (Prod.mk a)) := by
  simp only [flowCountPairUniverse, flow_count_join_erase, flow_count_map_erase,
    flow_count_finRange_erase, List.flatMap]

theorem flow_count_pair_universe_multiset (n : ℕ) :
    ((flowCountPairUniverse n).1 : Multiset (Fin n × Fin n)) =
      (Finset.univ : Finset (Fin n × Fin n)).val := by
  rw [flow_count_pair_universe_erase]
  change ((List.finRange n).flatMap (fun a => (List.finRange n).map (Prod.mk a)) :
    Multiset (Fin n × Fin n)) =
      (List.finRange n : Multiset (Fin n)) ×ˢ (List.finRange n : Multiset (Fin n))
  exact (Multiset.coe_product (List.finRange n) (List.finRange n)).symm

theorem flow_count_pair_universe_length (n : ℕ) :
    (flowCountPairUniverse n).1.length = n * n := by
  have hc := congrArg Multiset.card (flow_count_pair_universe_multiset n)
  simpa only [Multiset.coe_card, Finset.card_val, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin] using hc

theorem flow_count_pair_universe_bound (n : ℕ) :
    flowWorkTotal (flowCountPairUniverse n).2 ≤ 40 * (n + 1) ^ 2 := by
  have hrow : ∀ a : Fin n, flowWorkTotal
      (flowCountMap (fun b : Fin n => ((a, b), ({adminEvents := 1} : FlowWork)))
        (flowCountFinRange n).1).2 ≤ 7 * n + 2 := by
    intro a
    have h := flow_count_map_bound (fun b : Fin n =>
      ((a, b), ({adminEvents := 1} : FlowWork))) 1 (fun _ => le_rfl) (flowCountFinRange n).1
    simpa only [flow_count_finRange_erase, List.length_finRange, Nat.mul_comm] using h
  have hrows := flow_count_map_bound (fun a : Fin n => flowCountMap
    (fun b => ((a, b), ({adminEvents := 1} : FlowWork))) (flowCountFinRange n).1)
    (7 * n + 2) hrow (flowCountFinRange n).1
  have hleftLen := congrArg List.length (flow_count_finRange_erase n)
  simp only [List.length_finRange] at hleftLen
  rw [hleftLen] at hrows
  have hrowLen : ∀ row ∈ (flowCountMap (fun a : Fin n => flowCountMap
      (fun b => ((a, b), ({adminEvents := 1} : FlowWork))) (flowCountFinRange n).1)
      (flowCountFinRange n).1).1, row.length ≤ n := by
    intro row hmem
    rw [flow_count_map_erase] at hmem
    obtain ⟨a, _, he⟩ := List.mem_map.mp hmem
    subst row
    simp [flow_count_map_erase, flow_count_finRange_erase]
  have hj := flow_count_join_bound _ n hrowLen
  have hrowsLen : (flowCountMap (fun a : Fin n => flowCountMap
      (fun b => ((a, b), ({adminEvents := 1} : FlowWork))) (flowCountFinRange n).1)
      (flowCountFinRange n).1).1.length = n := by
    simp [flow_count_map_erase, flow_count_finRange_erase]
  rw [hrowsLen] at hj
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ _))) ≤ _
  repeat rw [flow_work_total_add]
  simp only [flow_count_finRange_total]
  nlinarith

def flowCountFilter {α : Type*} (p : α → FlowCounted Bool) (xs : List α) :
    FlowCounted (List α) := go xs []
where
  go : List α → List α → FlowCounted (List α)
    | [], acc =>
      let rev := flowCountReverseAux acc []
      (rev.1, flowWorkAdd {adminEvents := 1} rev.2)
    | a :: tail, acc =>
      let test := p a
      let rest := go tail (if test.1 then a :: acc else acc)
      (rest.1, flowWorkAdd test.2
        (flowWorkAdd {listEvents := if test.1 then 2 else 1, adminEvents := 1} rest.2))

theorem flow_count_filter_go_erase {α : Type*} (p : α → FlowCounted Bool)
    (xs acc : List α) :
    (flowCountFilter.go p xs acc).1 = List.filterTR.loop (fun a => (p a).1) xs acc := by
  induction xs generalizing acc with
  | nil => exact flow_count_reverse_aux_erase acc []
  | cons a xs ih =>
    cases he : (p a).1 <;> simpa [flowCountFilter.go, he, List.filterTR.loop] using
      ih (if (p a).1 then a :: acc else acc)

theorem flow_count_filter_erase {α : Type*} (p : α → FlowCounted Bool) (xs : List α) :
    (flowCountFilter p xs).1 = xs.filter (fun a => (p a).1) := by
  rw [List.filter_eq_filterTR]
  exact flow_count_filter_go_erase p xs []

theorem flow_count_filter_go_bound {α : Type*} (p : α → FlowCounted Bool)
    (B : ℕ) (hb : ∀ a, flowWorkTotal (p a).2 ≤ B) (xs acc : List α) :
    flowWorkTotal (flowCountFilter.go p xs acc).2 ≤
      xs.length * (B + 6) + 3 * acc.length + 2 := by
  induction xs generalizing acc with
  | nil =>
    have hr := flow_count_reverse_aux_total acc []
    change flowWorkTotal (flowWorkAdd _ (flowCountReverseAux acc []).2) ≤ _
    rw [flow_work_total_add, hr]
    change 1 + (3 * acc.length + 1) ≤ _
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    omega
  | cons a xs ih =>
    have hh := hb a
    cases he : (p a).1 with
    | false =>
      have ht := ih acc
      simp only [flowCountFilter.go, he, Bool.false_eq_true, ↓reduceIte]
      rw [flow_work_total_add, flow_work_total_add]
      change flowWorkTotal (p a).2 + (2 + flowWorkTotal (flowCountFilter.go p xs acc).2) ≤ _
      simp only [List.length_cons]
      nlinarith
    | true =>
      have ht := ih (a :: acc)
      simp only [flowCountFilter.go, he, ↓reduceIte]
      rw [flow_work_total_add, flow_work_total_add]
      change flowWorkTotal (p a).2 + (3 + flowWorkTotal (flowCountFilter.go p xs (a :: acc)).2) ≤ _
      simp only [List.length_cons] at ht ⊢
      nlinarith

theorem flow_count_filter_bound {α : Type*} (p : α → FlowCounted Bool)
    (B : ℕ) (hb : ∀ a, flowWorkTotal (p a).2 ≤ B) (xs : List α) :
    flowWorkTotal (flowCountFilter p xs).2 ≤ xs.length * (B + 6) + 2 := by
  simpa only [flowCountFilter, List.length_nil, mul_zero, add_zero] using
    flow_count_filter_go_bound p B hb xs []

def flowCountLength {α : Type*} : List α → FlowCounted ℕ
  | [] => (0, {adminEvents := 1})
  | _ :: tail =>
    let rest := flowCountLength tail
    (rest.1 + 1, flowWorkAdd {listEvents := 1, adminEvents := 1} rest.2)

theorem flow_count_length_erase {α : Type*} (xs : List α) :
    (flowCountLength xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [flowCountLength, List.length_cons] using congrArg (· + 1) ih

theorem flow_count_length_total {α : Type*} (xs : List α) :
    flowWorkTotal (flowCountLength xs).2 = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change flowWorkTotal (flowWorkAdd _ (flowCountLength xs).2) = _
    rw [flow_work_total_add, ih]
    change 2 + (2 * xs.length + 1) = _
    simp only [List.length_cons]
    omega

def flowCountGraphFuel {n : ℕ} (C : RationalFlowTable n) : FlowCounted ℕ :=
  let pairs := flowCountPairUniverse n
  let support := flowCountFilter (fun e =>
    (decide (0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1),
      {rationalEvents := 2, vectorEvents := 4, adminEvents := 1})) pairs.1
  let cardinal := flowCountLength support.1
  (cardinal.1 * (n + 2) + 1, flowWorkAdd pairs.2
    (flowWorkAdd support.2 (flowWorkAdd cardinal.2 {adminEvents := 3})))

theorem flow_count_graph_fuel_erase {n : ℕ} (C : RationalFlowTable n) :
    (flowCountGraphFuel C).1 = rationalTableGraphFuel C := by
  let P : Fin n × Fin n → Prop := fun e =>
    0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1
  have hm : ((flowCountFilter (fun e =>
      (decide (P e), ({rationalEvents := 2, vectorEvents := 4, adminEvents := 1} : FlowWork)))
      (flowCountPairUniverse n).1).1 : Multiset (Fin n × Fin n)) =
      (rationalCapacityArcSupport C).val := by
    rw [flow_count_filter_erase]
    change Multiset.filter P ((flowCountPairUniverse n).1 : Multiset _) = _
    rw [flow_count_pair_universe_multiset]
    rfl
  have hc := congrArg Multiset.card hm
  simp only [Multiset.coe_card, Finset.card_val] at hc
  change (flowCountLength _).1 * (n + 2) + 1 = _
  rw [flow_count_length_erase, hc]
  rfl

theorem flow_count_graph_fuel_bound {n : ℕ} (C : RationalFlowTable n) :
    flowWorkTotal (flowCountGraphFuel C).2 ≤ 100 * (n + 1) ^ 2 := by
  have hu := flow_count_pair_universe_bound n
  have hf := flow_count_filter_bound (fun e : Fin n × Fin n =>
    (decide (0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1),
      ({rationalEvents := 2, vectorEvents := 4, adminEvents := 1} : FlowWork))) 7
    (fun _ => le_rfl) (flowCountPairUniverse n).1
  rw [flow_count_pair_universe_length] at hf
  have hlen : (flowCountFilter (fun e : Fin n × Fin n =>
      (decide (0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1),
        ({rationalEvents := 2, vectorEvents := 4, adminEvents := 1} : FlowWork)))
      (flowCountPairUniverse n).1).1.length ≤ n * n := by
    rw [flow_count_filter_erase]
    exact le_trans (List.length_filter_le _ _) (le_of_eq (flow_count_pair_universe_length n))
  have hl := flow_count_length_total (flowCountFilter (fun e : Fin n × Fin n =>
    (decide (0 < rationalFlowTableEntry C e.1 e.2 + rationalFlowTableEntry C e.2 e.1),
      ({rationalEvents := 2, vectorEvents := 4, adminEvents := 1} : FlowWork)))
      (flowCountPairUniverse n).1).1
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ _))) ≤ _
  repeat rw [flow_work_total_add]
  change flowWorkTotal (flowCountPairUniverse n).2 +
    (flowWorkTotal (flowCountFilter _ (flowCountPairUniverse n).1).2 +
      (flowWorkTotal (flowCountLength _).2 + 3)) ≤ _
  nlinarith

def flowCountZeroTable (n : ℕ) : FlowCounted (RationalFlowTable n) :=
  flowCountVectorOfFn fun _ => flowCountVectorOfFn fun _ => (0, {})

theorem flow_count_zero_table_erase (n : ℕ) :
    (flowCountZeroTable n).1 = rationalZeroFlowTable n := by
  unfold flowCountZeroTable rationalZeroFlowTable
  rw [flow_count_vector_ofFn_erase]
  congr 1
  funext u
  exact flow_count_vector_ofFn_erase _

theorem flow_count_zero_table_bound (n : ℕ) :
    flowWorkTotal (flowCountZeroTable n).2 ≤ 10 * (n + 1) ^ 2 := by
  have hr : ∀ u : Fin n, flowWorkTotal
      (flowCountVectorOfFn (fun _ : Fin n => ((0 : ℚ), ({} : FlowWork)))).2 ≤ n * 4 + 1 := by
    intro u
    exact flow_count_vector_ofFn_bound _ 0 (fun _ => le_rfl)
  have ht := flow_count_vector_ofFn_bound
    (fun _ : Fin n => flowCountVectorOfFn (fun _ : Fin n => ((0 : ℚ), ({} : FlowWork))))
    (n * 4 + 1) hr
  change flowWorkTotal (flowCountZeroTable n).2 ≤ _ at ht
  nlinarith

def flowCountFindFlowPolynomial {n : ℕ} (C : RationalFlowTable n) (s t : Fin n) :
    FlowCounted (RationalFlowTable n) :=
  let fuel := flowCountGraphFuel C
  let initial := flowCountZeroTable n
  let run := flowCountTableFlowDirect C s t fuel.1 initial.1
  (run.1, flowWorkAdd fuel.2 (flowWorkAdd initial.2
    (flowWorkAdd {adminEvents := 1} run.2)))

theorem flow_count_find_flow_polynomial_erase {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) :
    (flowCountFindFlowPolynomial C s t).1 = rationalTableFindFlowPolynomial C s t := by
  change (flowCountTableFlowDirect C s t _ _).1 = _
  rw [flow_count_table_flow_direct_erase, flow_count_graph_fuel_erase, flow_count_zero_table_erase]
  rfl

/-- Complete source-event bound includes real graph-fuel and zero-table
initialization, the candidate checks, paths, all materialized pushes, and the
actual demanded direct-loop administrative cases. The erased output is the
actual graph-bounded finder. This is still a source-event unit-operation model,
not a theorem about compiler instructions, allocator behavior or rational bits.
-/
theorem flow_count_find_flow_polynomial_bound {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) :
    flowWorkTotal (flowCountFindFlowPolynomial C s t).2 ≤ 3000 * (n + 2) ^ 6 := by
  have hf := flow_count_graph_fuel_bound C
  have hz := flow_count_zero_table_bound n
  have hr := flow_count_graph_fuel_loop_bound C (rationalZeroFlowTable n) s t
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ _))) ≤ _
  repeat rw [flow_work_total_add]
  rw [flow_count_graph_fuel_erase, flow_count_zero_table_erase]
  change flowWorkTotal (flowCountGraphFuel C).2 + (flowWorkTotal (flowCountZeroTable n).2 +
    (1 + flowWorkTotal (flowCountTableFlowDirect C s t (rationalTableGraphFuel C) (rationalZeroFlowTable n)).2)) ≤ _
  have hpoly : (n + 1) ^ 2 ≤ (n + 2) ^ 6 := by
    have h1 : (n + 1) ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (n + 2) ^ 2 ≤ (n + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans h1 h2
  have hpos : 1 ≤ (n + 2) ^ 6 := by
    have he : 0 < (n + 2) ^ 6 := pow_pos (by omega) _
    omega
  omega

end SparseCompletion
