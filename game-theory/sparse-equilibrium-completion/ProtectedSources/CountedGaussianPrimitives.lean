/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact verification status is retained in external immutable receipts. Separate extension of the frozen flow82 ledger.
Gaussian.QVec is Mathlib's LIST-backed Vector, not core's Array-backed Vector.
List reads below execute and charge each traversed cons. Gaussian arithmetic
extends rationalEvents to mul/div/neg as well as add/sub/equality/order tests;
these are unit source invocations, never operand-bit or native instructions.

The finite-sum adapter retains canonical Fin enumeration, the pinned mapTR
writer from flow82, and the source foldr result. Its per-element fold charge
batches the independently pure toArray conversion used by foldrTR (list visit,
array push) with the corresponding array read/add/loop event. As in flow82's
join adapter, this is an aggregate designated ledger, not a trace-order or
operational-adequacy theorem. Counter bookkeeping itself is excluded.
-/
module
public import ProtectedSources.CountedFlowInitialization
public import ProtectedSources.RationalGaussianKernel
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Literal List.get recursion. Both terminal read and skipped cons cost one
list visit and one designated indexing/case event. No constant-time read. -/
def gaussianCountListGet {α : Type*} : (xs : List α) → Fin xs.length → FlowCounted α
  | a :: _, ⟨0, _⟩ => (a, {listEvents := 1, adminEvents := 1})
  | _ :: tail, ⟨i + 1, hi⟩ =>
    let rest := gaussianCountListGet tail ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    (rest.1, flowWorkAdd {listEvents := 1, adminEvents := 1} rest.2)

theorem gaussian_count_list_get_erase {α : Type*} (xs : List α) (i : Fin xs.length) :
    (gaussianCountListGet xs i).1 = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons a tail ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ i => exact ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem gaussian_count_list_get_total {α : Type*} (xs : List α) (i : Fin xs.length) :
    flowWorkTotal (gaussianCountListGet xs i).2 = 2 * (i.val + 1) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons a tail ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ i =>
      change flowWorkTotal (flowWorkAdd _ (gaussianCountListGet tail _).2) = _
      rw [flow_work_total_add, ih]
      change 2 + 2 * (i + 1) = 2 * (i + 1 + 1)
      omega

def gaussianCountVectorGet {α : Type*} {n : ℕ} (v : List.Vector α n) (i : Fin n) :
    FlowCounted α := gaussianCountListGet v.val (i.cast v.property.symm)

theorem gaussian_count_vector_get_erase {α : Type*} {n : ℕ}
    (v : List.Vector α n) (i : Fin n) :
    (gaussianCountVectorGet v i).1 = v.get i := by
  exact gaussian_count_list_get_erase _ _

theorem gaussian_count_vector_get_total {α : Type*} {n : ℕ}
    (v : List.Vector α n) (i : Fin n) :
    flowWorkTotal (gaussianCountVectorGet v i).2 = 2 * (i.val + 1) := by
  exact gaussian_count_list_get_total _ _

theorem gaussian_count_vector_get_bound {α : Type*} {n : ℕ}
    (v : List.Vector α n) (i : Fin n) :
    flowWorkTotal (gaussianCountVectorGet v i).2 ≤ 2 * n := by
  rw [gaussian_count_vector_get_total]
  omega

/-- Literal recursive Mathlib List.Vector.ofFn. Its subtype proofs erase;
there is no core Array.ofFn call or reverse pass at this site. -/
def gaussianCountVectorOfFn {α : Type*} : {n : ℕ} → (Fin n → FlowCounted α) →
    FlowCounted (List.Vector α n)
  | 0, _ => (List.Vector.nil, {listEvents := 1, adminEvents := 1})
  | n + 1, f =>
    let head := f 0
    let tail := gaussianCountVectorOfFn (fun i : Fin n => f i.succ)
    (List.Vector.cons head.1 tail.1,
      flowWorkAdd head.2 (flowWorkAdd {listEvents := 1, adminEvents := 1} tail.2))

theorem gaussian_count_vector_ofFn_erase {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) :
    (gaussianCountVectorOfFn f).1 = List.Vector.ofFn (fun i => (f i).1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change List.Vector.cons _ (gaussianCountVectorOfFn _).1 = _
    rw [ih]
    rfl

theorem gaussian_count_vector_ofFn_bound {α : Type*} {n : ℕ}
    (f : Fin n → FlowCounted α) (B : ℕ) (hb : ∀ i, flowWorkTotal (f i).2 ≤ B) :
    flowWorkTotal (gaussianCountVectorOfFn f).2 ≤ n * (B + 2) + 2 := by
  induction n with
  | zero => simp [gaussianCountVectorOfFn, flowWorkTotal]
  | succ n ih =>
    have hh := hb 0
    have ht := ih (fun i => f i.succ) (fun i => hb i.succ)
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
    rw [flow_work_total_add, flow_work_total_add]
    change flowWorkTotal (f 0).2 +
      (2 + flowWorkTotal (gaussianCountVectorOfFn (fun i : Fin n => f i.succ)).2) ≤ _
    nlinarith

def gaussianCountEntry {r n : ℕ} (A : Gaussian.QTable r n) (i : Fin r) (j : Fin n) :
    FlowCounted ℚ :=
  let row := gaussianCountVectorGet A i
  let cell := gaussianCountVectorGet row.1 j
  (cell.1, flowWorkAdd row.2 cell.2)

theorem gaussian_count_entry_erase {r n : ℕ} (A : Gaussian.QTable r n)
    (i : Fin r) (j : Fin n) :
    (gaussianCountEntry A i j).1 = Gaussian.entry A i j := by
  simp [gaussianCountEntry, gaussian_count_vector_get_erase, Gaussian.entry]

theorem gaussian_count_entry_total {r n : ℕ} (A : Gaussian.QTable r n)
    (i : Fin r) (j : Fin n) :
    flowWorkTotal (gaussianCountEntry A i j).2 = 2 * (i.val + 1) + 2 * (j.val + 1) := by
  change flowWorkTotal (flowWorkAdd _ _) = _
  rw [flow_work_total_add, gaussian_count_vector_get_total, gaussian_count_vector_get_total]

theorem gaussian_count_entry_bound {r n : ℕ} (A : Gaussian.QTable r n)
    (i : Fin r) (j : Fin n) :
    flowWorkTotal (gaussianCountEntry A i j).2 ≤ 2 * (r + n) := by
  rw [gaussian_count_entry_total]
  omega

/-- Same two nested list-vector constructions as Gaussian.tableOfFn. -/
def gaussianCountTableOfFn {r n : ℕ} (f : Fin r → Fin n → FlowCounted ℚ) :
    FlowCounted (Gaussian.QTable r n) :=
  gaussianCountVectorOfFn (fun i => gaussianCountVectorOfFn (f i))

theorem gaussian_count_table_ofFn_erase {r n : ℕ}
    (f : Fin r → Fin n → FlowCounted ℚ) :
    (gaussianCountTableOfFn f).1 = Gaussian.tableOfFn (fun i j => (f i j).1) := by
  simp only [gaussianCountTableOfFn, gaussian_count_vector_ofFn_erase, Gaussian.tableOfFn]

theorem gaussian_count_table_ofFn_bound {r n : ℕ}
    (f : Fin r → Fin n → FlowCounted ℚ) (B : ℕ)
    (hb : ∀ i j, flowWorkTotal (f i j).2 ≤ B) :
    flowWorkTotal (gaussianCountTableOfFn f).2 ≤ r * (n * (B + 2) + 4) + 2 := by
  exact gaussian_count_vector_ofFn_bound _ (n * (B + 2) + 2)
    (fun i => gaussian_count_vector_ofFn_bound (f i) B (hb i))

/-- Aggregate pinned foldrTR conversion/read/add ledger. Each demanded input
cons is traversed in this executable adapter; conversion events are batched.
One rational addition, list1, vector2, admin3 per element; terminal admin2. -/
def gaussianCountListSum : List ℚ → FlowCounted ℚ
  | [] => (0, {adminEvents := 2})
  | a :: tail =>
    let rest := gaussianCountListSum tail
    (a + rest.1,
      flowWorkAdd {rationalEvents := 1, listEvents := 1, vectorEvents := 2, adminEvents := 3} rest.2)

theorem gaussian_count_list_sum_erase (xs : List ℚ) :
    (gaussianCountListSum xs).1 = xs.sum := by
  induction xs with
  | nil => rfl
  | cons a tail ih => simp [gaussianCountListSum, ih]

theorem gaussian_count_list_sum_total (xs : List ℚ) :
    flowWorkTotal (gaussianCountListSum xs).2 = 7 * xs.length + 2 := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    change flowWorkTotal (flowWorkAdd _ _) = _
    rw [flow_work_total_add, ih]
    change 7 + (7 * tail.length + 2) = _
    simp only [List.length_cons]
    omega

def gaussianCountFiniteSum {n : ℕ} (f : Fin n → FlowCounted ℚ) : FlowCounted ℚ :=
  let labels := flowCountFinRange n
  let values := flowCountMap f labels.1
  let total := gaussianCountListSum values.1
  (total.1, flowWorkAdd labels.2 (flowWorkAdd values.2 total.2))

theorem gaussian_count_finite_sum_erase {n : ℕ} (f : Fin n → FlowCounted ℚ) :
    (gaussianCountFiniteSum f).1 = ∑ j, (f j).1 := by
  change (gaussianCountListSum _).1 = _
  rw [gaussian_count_list_sum_erase, flow_count_map_erase, flow_count_finRange_erase]
  have hm : ((List.finRange n : List (Fin n)) : Multiset (Fin n)) =
      (Finset.univ : Finset (Fin n)).val := rfl
  change (Multiset.map (fun j => (f j).1) (List.finRange n : Multiset (Fin n))).sum = _
  rw [hm]
  rfl

theorem gaussian_count_finite_sum_bound {n : ℕ} (f : Fin n → FlowCounted ℚ)
    (B : ℕ) (hb : ∀ j, flowWorkTotal (f j).2 ≤ B) :
    flowWorkTotal (gaussianCountFiniteSum f).2 ≤ n * (B + 15) + 5 := by
  have hm := flow_count_map_bound f B hb (flowCountFinRange n).1
  have hs := gaussian_count_list_sum_total (flowCountMap f (flowCountFinRange n).1).1
  have hl : (flowCountFinRange n).1.length = n := by
    simp [flow_count_finRange_erase]
  rw [hl] at hm
  have hv : (flowCountMap f (flowCountFinRange n).1).1.length = n := by
    simp [flow_count_map_erase, flow_count_finRange_erase]
  rw [hv] at hs
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
  rw [flow_work_total_add, flow_work_total_add, flow_count_finRange_total, hs]
  nlinarith

end SparseCompletion
