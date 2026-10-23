/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCOMPILED cost-model foundation, separate from the checked graph34.
Counts designated source-level primitive events, not machine instructions or
operand-bit work. Instrumentation overhead itself is excluded, as in a writer
translation. Every measured count below is computed from the executable input
and executed branches; no progress/budget/bound is a field of a returned value.
The ledger is an aggregate of designated events. Value erasure and these
commutative totals do not assert execution-trace order or operational cost
adequacy for generated code; those are separate obligations.

The finite-vector adapter mirrors the actual countdown Array.ofFn.go loop,
including its order of calls to f, pushes, and decreasing loop index. Its
charge is accumulated while executing those same finite cases; it is not a
bound inserted into a result field. Counter bookkeeping is instrumentation.
-/
module
public import RationalTableFlowPolynomial
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure FlowWork where
  rationalEvents : ℕ := 0
  listEvents : ℕ := 0
  vectorEvents : ℕ := 0
  adminEvents : ℕ := 0
  deriving DecidableEq, Repr

def flowWorkAdd (a b : FlowWork) : FlowWork :=
  { rationalEvents := a.rationalEvents + b.rationalEvents
    listEvents := a.listEvents + b.listEvents
    vectorEvents := a.vectorEvents + b.vectorEvents
    adminEvents := a.adminEvents + b.adminEvents }

def flowWorkTotal (a : FlowWork) : ℕ :=
  a.rationalEvents + a.listEvents + a.vectorEvents + a.adminEvents

theorem flow_work_total_add (a b : FlowWork) :
    flowWorkTotal (flowWorkAdd a b) = flowWorkTotal a + flowWorkTotal b := by
  simp only [flowWorkAdd, flowWorkTotal]
  omega

def flowSumWork (xs : List FlowWork) : FlowWork :=
  xs.foldr flowWorkAdd {}

theorem flow_sum_work_total (xs : List FlowWork) :
    flowWorkTotal (flowSumWork xs) = (xs.map flowWorkTotal).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [flowSumWork, List.foldr_cons, flow_work_total_add, List.map_cons,
      List.sum_cons, ← ih]

theorem flow_sum_work_bound (xs : List FlowWork) (B : ℕ)
    (hb : ∀ a ∈ xs, flowWorkTotal a ≤ B) :
    flowWorkTotal (flowSumWork xs) ≤ xs.length * B := by
  induction xs with
  | nil => simp [flowSumWork, flowWorkTotal]
  | cons x xs ih =>
    have hx := hb x List.mem_cons_self
    have ht := ih (fun a ha => hb a (List.mem_cons_of_mem x ha))
    change flowWorkTotal (flowWorkAdd x (flowSumWork xs)) ≤ (xs.length + 1) * B
    rw [flow_work_total_add]
    nlinarith

abbrev FlowCounted (α : Type*) := α × FlowWork

/- Shared collection primitives. All callers, including BFS, use this one
appendTR pricing: each reverse cons has two list events and one control event. -/
def flowCountReverseAux {α : Type*} : List α → List α → FlowCounted (List α)
  | [], acc => (acc, {adminEvents := 1})
  | a :: xs, acc =>
    let rest := flowCountReverseAux xs (a :: acc)
    (rest.1, flowWorkAdd {listEvents := 2, adminEvents := 1} rest.2)

theorem flow_count_reverse_aux_erase {α : Type*} (xs acc : List α) :
    (flowCountReverseAux xs acc).1 = List.reverseAux xs acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih => exact ih (a :: acc)

theorem flow_count_reverse_aux_total {α : Type*} (xs acc : List α) :
    flowWorkTotal (flowCountReverseAux xs acc).2 = 3 * xs.length + 1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    change flowWorkTotal (flowWorkAdd _ (flowCountReverseAux xs (a :: acc)).2) = _
    rw [flow_work_total_add, ih]
    simp only [flowWorkTotal, List.length_cons]
    omega

def flowCountAppend {α : Type*} (xs ys : List α) : FlowCounted (List α) :=
  let first := flowCountReverseAux xs []
  let second := flowCountReverseAux first.1 ys
  (second.1, flowWorkAdd first.2 second.2)

theorem flow_count_append_erase {α : Type*} (xs ys : List α) :
    (flowCountAppend xs ys).1 = xs ++ ys := by
  change (flowCountReverseAux _ _).1 = _
  rw [flow_count_reverse_aux_erase, flow_count_reverse_aux_erase]
  change List.appendTR xs ys = xs ++ ys
  have he := congrFun (congrFun (congrFun List.append_eq_appendTR α) xs) ys
  exact he.symm

theorem flow_count_append_total {α : Type*} (xs ys : List α) :
    flowWorkTotal (flowCountAppend xs ys).2 = 6 * xs.length + 2 := by
  have hfirst := flow_count_reverse_aux_total xs []
  have hsecond := flow_count_reverse_aux_total (flowCountReverseAux xs []).1 ys
  have hlen : (flowCountReverseAux xs []).1.length = xs.length := by
    rw [flow_count_reverse_aux_erase]
    simp only [List.reverseAux_eq, List.append_nil, List.length_reverse]
  rw [hlen] at hsecond
  change flowWorkTotal (flowWorkAdd _ _) = _
  rw [flow_work_total_add]
  omega

/-- Same source countdown loop as Array.ofFn.go: one f call and one array
push per successor. Administrative events charge the loop case and the two
natural subtractions in n-i-1. The zero case charges one loop case. -/
def flowCountArrayOfFn {α : Type*} {n : ℕ} (f : Fin n → FlowCounted α) :
    FlowCounted (Array α) :=
  go (Array.emptyWithCapacity n) n (Nat.le_refl n)
where
  go (acc : Array α) : (i : ℕ) → i ≤ n → FlowCounted (Array α)
    | 0, _ => (acc, {adminEvents := 1})
    | i + 1, h =>
      have hi : n - i - 1 < n :=
        Nat.lt_of_lt_of_le (Nat.sub_one_lt (Nat.sub_ne_zero_iff_lt.mpr h)) (Nat.sub_le n i)
      let cell := f ⟨n - i - 1, hi⟩
      let rest := go (acc.push cell.1) i (Nat.le_of_succ_le h)
      (rest.1, flowWorkAdd cell.2
        (flowWorkAdd {vectorEvents := 1, adminEvents := 3} rest.2))

theorem flow_count_array_go_erase {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) (acc : Array α) (i : ℕ) (hi : i ≤ n) :
    (flowCountArrayOfFn.go f acc i hi).1 =
      Array.ofFn.go (fun j => (f j).1) acc i hi := by
  revert hi
  induction i generalizing acc with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    have hj : n - i - 1 < n := by omega
    simpa only [flowCountArrayOfFn.go, Array.ofFn.go] using
      ih (acc.push (f ⟨n - i - 1, hj⟩).1) (Nat.le_of_succ_le hi)

theorem flow_count_array_ofFn_erase {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) :
    (flowCountArrayOfFn f).1 = Array.ofFn (fun i => (f i).1) :=
  flow_count_array_go_erase f (Array.emptyWithCapacity n) n (Nat.le_refl n)

theorem flow_count_array_go_bound {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) (B : ℕ)
    (hb : ∀ i, flowWorkTotal (f i).2 ≤ B)
    (acc : Array α) (i : ℕ) (hi : i ≤ n) :
    flowWorkTotal (flowCountArrayOfFn.go f acc i hi).2 ≤ i * (B + 4) + 1 := by
  revert hi
  induction i generalizing acc with
  | zero => intro hi; simp [flowCountArrayOfFn.go, flowWorkTotal]
  | succ i ih =>
    intro hi
    have hj : n - i - 1 < n := by omega
    have hc := hb ⟨n - i - 1, hj⟩
    have ht := ih (acc.push (f ⟨n - i - 1, hj⟩).1) (Nat.le_of_succ_le hi)
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
    rw [flow_work_total_add, flow_work_total_add]
    change flowWorkTotal (f ⟨n - i - 1, hj⟩).2 +
      (4 + flowWorkTotal (flowCountArrayOfFn.go f
        (acc.push (f ⟨n - i - 1, hj⟩).1) i (Nat.le_of_succ_le hi)).2) ≤ _
    nlinarith

def flowCountVectorOfFn {α : Type*} {n : ℕ} (f : Fin n → FlowCounted α) :
    FlowCounted (Vector α n) :=
  let run := flowCountArrayOfFn f
  (⟨run.1, by rw [flow_count_array_ofFn_erase]; exact Array.size_ofFn⟩, run.2)

theorem flow_count_vector_ofFn_erase {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) :
    (flowCountVectorOfFn f).1 = Vector.ofFn (fun i => (f i).1) := by
  apply Vector.toArray_inj.mp
  exact flow_count_array_ofFn_erase f

theorem flow_count_vector_ofFn_bound {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) (B : ℕ)
    (hb : ∀ i, flowWorkTotal (f i).2 ≤ B) :
    flowWorkTotal (flowCountVectorOfFn f).2 ≤ n * (B + 4) + 1 :=
  flow_count_array_go_bound f B hb (Array.emptyWithCapacity n) n (Nat.le_refl n)

/-- Exact source countdown from Fin.foldr, used by List.finRange. -/
def flowCountFinRange (n : ℕ) : FlowCounted (List (Fin n)) :=
  go n (Nat.le_refl n) []
where
  go : (i : ℕ) → i ≤ n → List (Fin n) → FlowCounted (List (Fin n))
    | 0, _, acc => (acc, {adminEvents := 1})
    | i + 1, h, acc =>
      let rest := go i (Nat.le_of_lt h) (⟨i, h⟩ :: acc)
      (rest.1, flowWorkAdd {listEvents := 1, adminEvents := 1} rest.2)

theorem flow_count_finRange_go_erase (n i : ℕ) (hi : i ≤ n) (acc : List (Fin n)) :
    (flowCountFinRange.go n i hi acc).1 =
      Fin.foldr.loop n (fun j xs => j :: xs) i hi acc := by
  revert hi acc
  induction i with
  | zero => intro hi acc; rfl
  | succ i ih =>
    intro hi acc
    simpa only [flowCountFinRange.go, Fin.foldr.loop] using
      ih (Nat.le_of_lt hi) (⟨i, hi⟩ :: acc)

theorem flow_count_finRange_erase (n : ℕ) :
    (flowCountFinRange n).1 = List.finRange n :=
  flow_count_finRange_go_erase n n (Nat.le_refl n) []

theorem flow_count_finRange_go_total (n i : ℕ) (hi : i ≤ n) (acc : List (Fin n)) :
    flowWorkTotal (flowCountFinRange.go n i hi acc).2 = 2 * i + 1 := by
  revert hi acc
  induction i with
  | zero => intro hi acc; rfl
  | succ i ih =>
    intro hi acc
    have ht := ih (Nat.le_of_lt hi) (⟨i, hi⟩ :: acc)
    change flowWorkTotal (flowWorkAdd _ _) = _
    rw [flow_work_total_add, ht]
    change 2 + (2 * i + 1) = 2 * (i + 1) + 1
    omega

theorem flow_count_finRange_total (n : ℕ) :
    flowWorkTotal (flowCountFinRange n).2 = 2 * n + 1 :=
  flow_count_finRange_go_total n n (Nat.le_refl n) []

/-- Residual cache adapter: each cell performs the same rational subtraction
and positivity comparison, with four materialized input-table reads. -/
def flowCountResidualCache {n : ℕ} (C F : RationalFlowTable n) :
    FlowCounted (CachedBFSAdj n) :=
  flowCountVectorOfFn fun u => flowCountVectorOfFn fun v =>
    (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F) u v,
      {rationalEvents := 2, vectorEvents := 4, adminEvents := 1})

theorem flow_count_residual_cache_erase {n : ℕ} (C F : RationalFlowTable n) :
    (flowCountResidualCache C F).1 =
      cacheResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F) := by
  unfold flowCountResidualCache
  rw [flow_count_vector_ofFn_erase]
  unfold cacheResidualAdj
  congr 1
  funext u
  exact flow_count_vector_ofFn_erase _

theorem flow_count_residual_cache_bound {n : ℕ} (C F : RationalFlowTable n) :
    flowWorkTotal (flowCountResidualCache C F).2 ≤ 16 * (n + 1) ^ 2 := by
  have hrow : ∀ u : Fin n, flowWorkTotal (flowCountVectorOfFn (fun v =>
      (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F) u v,
        {rationalEvents := 2, vectorEvents := 4, adminEvents := 1}))).2 ≤ n * 11 + 1 := by
    intro u
    apply flow_count_vector_ofFn_bound _ 7
    intro v
    exact le_rfl
  have ht := flow_count_vector_ofFn_bound
    (fun u => flowCountVectorOfFn (fun v =>
      (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F) u v,
        {rationalEvents := 2, vectorEvents := 4, adminEvents := 1}))) (n * 11 + 1) hrow
  change flowWorkTotal (flowCountResidualCache C F).2 ≤ _ at ht
  nlinarith

end SparseCompletion
