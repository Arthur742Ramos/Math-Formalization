/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCOMPILED. Executable writer translations of the actual path
residual list, attained minimum, and fully materialized rational table push.
Counts rational primitive invocations and designated list/vector/admin events;
no claim about rational operand bits or machine allocation/copy time.
-/
module
public import CountedCachedBFS
@[expose] public section
namespace SparseCompletion

def flowCountPathResiduals {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) : FlowCounted (List ℚ) :=
  List.rec (motive := fun _ => Fin n → FlowCounted (List ℚ))
    (fun _ => ([], {listEvents := 1, adminEvents := 1}))
    (fun b _ ih start =>
      let residual := rationalFlowTableEntry C start b - rationalFlowTableEntry F start b
      let rest := ih b
      (residual :: rest.1,
        flowWorkAdd {rationalEvents := 1, listEvents := 2, vectorEvents := 4, adminEvents := 2} rest.2)) tail a

theorem flow_count_path_residuals_erase {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) :
    (flowCountPathResiduals C F a tail).1 =
      rationalPathResiduals (rationalFlowTableEntry C) (rationalFlowTableEntry F) a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    change (_ :: (flowCountPathResiduals C F b tail).1) = _
    rw [ih b]
    rfl

theorem flow_count_path_residuals_length {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) :
    (flowCountPathResiduals C F a tail).1.length = tail.length := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    change (flowCountPathResiduals C F b tail).1.length + 1 = tail.length + 1
    rw [ih b]

theorem flow_count_path_residuals_total {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) :
    flowWorkTotal (flowCountPathResiduals C F a tail).2 = 9 * tail.length + 2 := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    change flowWorkTotal (flowWorkAdd _ (flowCountPathResiduals C F b tail).2) = _
    rw [flow_work_total_add, ih b]
    simp only [flowWorkTotal, List.length_cons]
    omega

def flowCountNonemptyMinimum (xs : List ℚ) : FlowCounted (Option ℚ) :=
  List.rec (none, {listEvents := 1, adminEvents := 1})
    (fun z _ ih =>
      match ih.1 with
      | none => (some z, flowWorkAdd {listEvents := 1, adminEvents := 2} ih.2)
      | some b =>
        (some (min z b), flowWorkAdd {rationalEvents := 1, listEvents := 1, adminEvents := 2} ih.2)) xs

theorem flow_count_nonempty_minimum_erase (xs : List ℚ) :
    (flowCountNonemptyMinimum xs).1 = rationalNonemptyMinimum xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    have he : flowCountNonemptyMinimum (z :: zs) =
        (match (flowCountNonemptyMinimum zs).1 with
        | none => (some z, flowWorkAdd {listEvents := 1, adminEvents := 2}
            (flowCountNonemptyMinimum zs).2)
        | some b => (some (min z b), flowWorkAdd
            {rationalEvents := 1, listEvents := 1, adminEvents := 2}
            (flowCountNonemptyMinimum zs).2)) := rfl
    rw [he]
    change _ = some (Option.rec (motive := fun _ => ℚ) z
      (fun b => min z b) (rationalNonemptyMinimum zs))
    rw [← ih]
    cases hm : (flowCountNonemptyMinimum zs).1 <;> rfl

theorem flow_count_nonempty_minimum_bound (xs : List ℚ) :
    flowWorkTotal (flowCountNonemptyMinimum xs).2 ≤ 4 * xs.length + 2 := by
  induction xs with
  | nil => simp [flowCountNonemptyMinimum, flowWorkTotal]
  | cons z zs ih =>
    have he : flowCountNonemptyMinimum (z :: zs) =
        (match (flowCountNonemptyMinimum zs).1 with
        | none => (some z, flowWorkAdd {listEvents := 1, adminEvents := 2}
            (flowCountNonemptyMinimum zs).2)
        | some b => (some (min z b), flowWorkAdd
            {rationalEvents := 1, listEvents := 1, adminEvents := 2}
            (flowCountNonemptyMinimum zs).2)) := rfl
    rw [he]
    cases hm : (flowCountNonemptyMinimum zs).1 with
    | none =>
      change flowWorkTotal (flowWorkAdd _ (flowCountNonemptyMinimum zs).2) ≤ _
      rw [flow_work_total_add]
      change 3 + flowWorkTotal (flowCountNonemptyMinimum zs).2 ≤ _
      simp only [List.length_cons]
      omega
    | some b =>
      change flowWorkTotal (flowWorkAdd _ (flowCountNonemptyMinimum zs).2) ≤ _
      rw [flow_work_total_add]
      change 4 + flowWorkTotal (flowCountNonemptyMinimum zs).2 ≤ _
      simp only [List.length_cons]
      omega

def flowCountPathBottleneck {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) : FlowCounted (Option ℚ) :=
  let residuals := flowCountPathResiduals C F a tail
  let amount := flowCountNonemptyMinimum residuals.1
  (amount.1, flowWorkAdd residuals.2 amount.2)

theorem flow_count_path_bottleneck_erase {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) :
    (flowCountPathBottleneck C F a tail).1 =
      rationalPathBottleneck (rationalFlowTableEntry C) (rationalFlowTableEntry F) a tail := by
  change (flowCountNonemptyMinimum _).1 = _
  rw [flow_count_nonempty_minimum_erase, flow_count_path_residuals_erase]
  rfl

theorem flow_count_path_bottleneck_bound {n : ℕ} (C F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) :
    flowWorkTotal (flowCountPathBottleneck C F a tail).2 ≤ 13 * tail.length + 4 := by
  have hr := flow_count_path_residuals_total C F a tail
  have hm := flow_count_nonempty_minimum_bound (flowCountPathResiduals C F a tail).1
  rw [flow_count_path_residuals_length] at hm
  change flowWorkTotal (flowWorkAdd _ _) ≤ _
  rw [flow_work_total_add]
  omega

/-- Original net-edge cell always executes its rational add and subtract.
The two proposition conjunctions each evaluate two Fin equalities. -/
def flowCountTablePushEdge {n : ℕ} (F : RationalFlowTable n)
    (a b : Fin n) (δ : ℚ) : FlowCounted (RationalFlowTable n) :=
  flowCountVectorOfFn fun u => flowCountVectorOfFn fun v =>
    (rationalNetPushEdge (rationalFlowTableEntry F) a b δ u v,
      {rationalEvents := 2, vectorEvents := 2, adminEvents := 8})

theorem flow_count_table_push_edge_erase {n : ℕ} (F : RationalFlowTable n)
    (a b : Fin n) (δ : ℚ) :
    (flowCountTablePushEdge F a b δ).1 = rationalTablePushEdge F a b δ := by
  unfold flowCountTablePushEdge rationalTablePushEdge
  rw [flow_count_vector_ofFn_erase]
  congr 1
  funext u
  exact flow_count_vector_ofFn_erase _

theorem flow_count_table_push_edge_bound {n : ℕ} (F : RationalFlowTable n)
    (a b : Fin n) (δ : ℚ) :
    flowWorkTotal (flowCountTablePushEdge F a b δ).2 ≤ 24 * (n + 1) ^ 2 := by
  have hrow : ∀ u : Fin n, flowWorkTotal (flowCountVectorOfFn (fun v =>
      (rationalNetPushEdge (rationalFlowTableEntry F) a b δ u v,
        {rationalEvents := 2, vectorEvents := 2, adminEvents := 8}))).2 ≤ n * 16 + 1 := by
    intro u
    apply flow_count_vector_ofFn_bound _ 12
    intro v
    exact le_rfl
  have ht := flow_count_vector_ofFn_bound
    (fun u => flowCountVectorOfFn (fun v =>
      (rationalNetPushEdge (rationalFlowTableEntry F) a b δ u v,
        {rationalEvents := 2, vectorEvents := 2, adminEvents := 8}))) (n * 16 + 1) hrow
  change flowWorkTotal (flowCountTablePushEdge F a b δ).2 ≤ _ at ht
  nlinarith

def flowCountTablePushPath {n : ℕ} (F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) : FlowCounted (RationalFlowTable n) :=
  List.rec (motive := fun _ => Fin n → FlowCounted (RationalFlowTable n))
    (fun _ => (F, {listEvents := 1, adminEvents := 1}))
    (fun b _ ih start =>
      let rest := ih b
      let pushed := flowCountTablePushEdge rest.1 start b δ
      (pushed.1, flowWorkAdd rest.2
        (flowWorkAdd {listEvents := 1, adminEvents := 2} pushed.2))) tail a

theorem flow_count_table_push_path_erase {n : ℕ} (F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) :
    (flowCountTablePushPath F a tail δ).1 = rationalTablePushPath F a tail δ := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    change (flowCountTablePushEdge (flowCountTablePushPath F b tail δ).1 a b δ).1 = _
    rw [flow_count_table_push_edge_erase, ih b]
    rfl

theorem flow_count_table_push_path_bound {n : ℕ} (F : RationalFlowTable n)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) :
    flowWorkTotal (flowCountTablePushPath F a tail δ).2 ≤
      tail.length * (24 * (n + 1) ^ 2 + 3) + 2 := by
  induction tail generalizing a with
  | nil => simp [flowCountTablePushPath, flowWorkTotal]
  | cons b tail ih =>
    have hp := flow_count_table_push_edge_bound (flowCountTablePushPath F b tail δ).1 a b δ
    have ht := ih b
    change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ _)) ≤ _
    rw [flow_work_total_add, flow_work_total_add]
    change flowWorkTotal (flowCountTablePushPath F b tail δ).2 +
      (3 + flowWorkTotal (flowCountTablePushEdge (flowCountTablePushPath F b tail δ).1 a b δ).2) ≤ _
    simp only [List.length_cons]
    nlinarith

end SparseCompletion
