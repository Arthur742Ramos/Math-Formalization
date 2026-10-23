/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCOMPILED. The checked wrapper's actual candidate decision is
translated at the pinned instance computation order: eager conjunction checks,
tail-first List.instDecidablePairwise, head-first List.decidableBAll, actual
getLast traversal, and reconstruction of the positive residual list.
-/
module
public import CountedRationalPathOps
@[expose] public section
namespace SparseCompletion

def flowCountAll {α : Type*} (p : α → FlowCounted Bool) : List α → FlowCounted Bool
  | [] => (true, {listEvents := 1})
  | a :: tail =>
    let head := p a
    if head.1 then
      let rest := flowCountAll p tail
      (rest.1, flowWorkAdd head.2 (flowWorkAdd {listEvents := 1, adminEvents := 1} rest.2))
    else (false, flowWorkAdd head.2 {listEvents := 1, adminEvents := 1})

theorem flow_count_all_erase {α : Type*} (p : α → FlowCounted Bool)
    (P : α → Prop) [DecidablePred P] (hp : ∀ a, (p a).1 = decide (P a)) (xs : List α) :
    (flowCountAll p xs).1 = decide (∀ a ∈ xs, P a) := by
  induction xs with
  | nil => simp [flowCountAll]
  | cons a tail ih =>
    by_cases h : P a <;> simp [flowCountAll, hp a, ih, h]

theorem flow_count_all_bound {α : Type*} (p : α → FlowCounted Bool)
    (B : ℕ) (hb : ∀ a, flowWorkTotal (p a).2 ≤ B) (xs : List α) :
    flowWorkTotal (flowCountAll p xs).2 ≤ xs.length * (B + 2) + 1 := by
  induction xs with
  | nil => simp [flowCountAll, flowWorkTotal]
  | cons a tail ih =>
    have hh := hb a
    cases he : (p a).1 with
    | false =>
      simp only [flowCountAll, he, Bool.false_eq_true, ↓reduceIte]
      rw [flow_work_total_add]
      change flowWorkTotal (p a).2 + 2 ≤ _
      simp only [List.length_cons]
      nlinarith
    | true =>
      simp only [flowCountAll, he, ↓reduceIte]
      rw [flow_work_total_add, flow_work_total_add]
      change flowWorkTotal (p a).2 + (2 + flowWorkTotal (flowCountAll p tail).2) ≤ _
      simp only [List.length_cons]
      nlinarith

/-- Same tail-first order as the pinned Pairwise/Nodup decision instance. -/
def flowCountNodup {α : Type*} [DecidableEq α] : List α → FlowCounted Bool
  | [] => (true, {listEvents := 1, adminEvents := 1})
  | a :: tail =>
    let rest := flowCountNodup tail
    if rest.1 then
      let heads := flowCountAll (fun b => (decide (a ≠ b), {adminEvents := 1})) tail
      (heads.1, flowWorkAdd rest.2
        (flowWorkAdd {listEvents := 1, adminEvents := 1} heads.2))
    else (false, flowWorkAdd rest.2 {listEvents := 1, adminEvents := 1})

theorem flow_count_nodup_erase {α : Type*} [DecidableEq α] (xs : List α) :
    (flowCountNodup xs).1 = decide xs.Nodup := by
  induction xs with
  | nil => simp [flowCountNodup]
  | cons a tail ih =>
    have ha := flow_count_all_erase
      (fun b => (decide (a ≠ b), ({adminEvents := 1} : FlowWork)))
      (fun b => a ≠ b) (fun _ => rfl) tail
    by_cases h : tail.Nodup
    · simp only [flowCountNodup, ih, decide_eq_true h, ↓reduceIte]
      rw [ha]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, List.nodup_cons]
      constructor
      · intro hh
        exact ⟨by intro hm; exact hh a hm rfl, h⟩
      · intro hh b hb he
        subst b
        exact hh.1 hb
    · simp [flowCountNodup, ih, h, List.nodup_cons]

theorem flow_count_nodup_bound {α : Type*} [DecidableEq α] (xs : List α) :
    flowWorkTotal (flowCountNodup xs).2 ≤ 4 * (xs.length + 1) ^ 2 := by
  induction xs with
  | nil => simp only [flowCountNodup, flowWorkTotal, List.length_nil]; omega
  | cons a tail ih =>
    have ha := flow_count_all_bound
      (fun b => (decide (a ≠ b), ({adminEvents := 1} : FlowWork))) 1 (fun _ => le_rfl) tail
    cases ht : (flowCountNodup tail).1 with
    | false =>
      simp only [flowCountNodup, ht, Bool.false_eq_true, ↓reduceIte]
      rw [flow_work_total_add]
      change flowWorkTotal (flowCountNodup tail).2 + 2 ≤ _
      simp only [List.length_cons]
      nlinarith
    | true =>
      simp only [flowCountNodup, ht, ↓reduceIte]
      rw [flow_work_total_add, flow_work_total_add]
      change flowWorkTotal (flowCountNodup tail).2 + (2 + flowWorkTotal (flowCountAll _ tail).2) ≤ _
      simp only [List.length_cons]
      nlinarith

def flowCountGetLast {α : Type*} (a : α) : List α → FlowCounted α
  | [] => (a, {listEvents := 1, adminEvents := 1})
  | b :: tail =>
    let rest := flowCountGetLast b tail
    (rest.1, flowWorkAdd {listEvents := 2, adminEvents := 1} rest.2)

theorem flow_count_getLast_erase {α : Type*} (a : α) (tail : List α) :
    (flowCountGetLast a tail).1 = (a :: tail).getLast (by simp) := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih => exact ih b

theorem flow_count_getLast_total {α : Type*} (a : α) (tail : List α) :
    flowWorkTotal (flowCountGetLast a tail).2 = 3 * tail.length + 2 := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    change flowWorkTotal (flowWorkAdd _ (flowCountGetLast b tail).2) = _
    rw [flow_work_total_add, ih b]
    simp only [flowWorkTotal, List.length_cons]
    omega

def flowCountHeadCheck {n : ℕ} (s : Fin n) : List (Fin n) → FlowCounted Bool
  | [] => (false, {listEvents := 1, adminEvents := 1})
  | a :: _ => (decide (a = s), {listEvents := 1, adminEvents := 2})

theorem flow_count_head_check_erase {n : ℕ} (s : Fin n) (path : List (Fin n)) :
    (flowCountHeadCheck s path).1 = decide (path.head? = some s) := by
  cases path <;> simp [flowCountHeadCheck]

def flowCountLastCheck {n : ℕ} (t : Fin n) : List (Fin n) → FlowCounted Bool
  | [] => (false, {listEvents := 1, adminEvents := 1})
  | a :: tail =>
    let last := flowCountGetLast a tail
    (decide (last.1 = t), flowWorkAdd {listEvents := 1, adminEvents := 2} last.2)

theorem flow_count_last_check_erase {n : ℕ} (t : Fin n) (path : List (Fin n)) :
    (flowCountLastCheck t path).1 = decide (path.getLast? = some t) := by
  cases path with
  | nil => rfl
  | cons a tail => simp [flowCountLastCheck, flow_count_getLast_erase, List.getLast?]

def flowCountPositiveResiduals {n : ℕ} (C F : RationalFlowTable n)
    (s : Fin n) (tail : List (Fin n)) : FlowCounted Bool :=
  let residuals := flowCountPathResiduals C F s tail
  let positive := flowCountAll
    (fun z => (decide (0 < z), {rationalEvents := 1})) residuals.1
  (positive.1, flowWorkAdd residuals.2 positive.2)

theorem flow_count_positive_residuals_erase {n : ℕ} (C F : RationalFlowTable n)
    (s : Fin n) (tail : List (Fin n)) :
    (flowCountPositiveResiduals C F s tail).1 =
      decide (∀ z ∈ rationalPathResiduals (rationalFlowTableEntry C)
        (rationalFlowTableEntry F) s tail, 0 < z) := by
  change (flowCountAll _ _).1 = _
  rw [flow_count_all_erase _ (fun z : ℚ => 0 < z) (fun _ => rfl),
    flow_count_path_residuals_erase]

theorem flow_count_positive_residuals_bound {n : ℕ} (C F : RationalFlowTable n)
    (s : Fin n) (tail : List (Fin n)) :
    flowWorkTotal (flowCountPositiveResiduals C F s tail).2 ≤ 12 * tail.length + 3 := by
  have hr := flow_count_path_residuals_total C F s tail
  have hp := flow_count_all_bound
    (fun z : ℚ => (decide (0 < z), ({rationalEvents := 1} : FlowWork))) 1
    (fun _ => le_rfl) (flowCountPathResiduals C F s tail).1
  rw [flow_count_path_residuals_length] at hp
  change flowWorkTotal (flowWorkAdd _ _) ≤ _
  rw [flow_work_total_add]
  omega

/-- The four input decisions are let-bound eagerly, matching the source And
instance. In particular the residual list is not skipped on a false head test.
-/
def flowCountAugmentCandidate {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (path : List (Fin n)) : FlowCounted Bool :=
  let head := flowCountHeadCheck s path
  let last := flowCountLastCheck t path
  let nodup := flowCountNodup path
  let positive := flowCountPositiveResiduals C F s path.tail
  (head.1 && last.1 && nodup.1 && positive.1,
    flowWorkAdd head.2 (flowWorkAdd last.2 (flowWorkAdd nodup.2
      (flowWorkAdd positive.2 {adminEvents := 3}))))

theorem flow_count_augment_candidate_erase {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (path : List (Fin n)) :
    (flowCountAugmentCandidate C F s t path).1 = decide (RationalAugmentCandidate C F s t path) := by
  apply Bool.eq_iff_iff.mpr
  simp [flowCountAugmentCandidate, flow_count_head_check_erase, flow_count_last_check_erase,
    flow_count_nodup_erase, flow_count_positive_residuals_erase, RationalAugmentCandidate, and_assoc]

theorem flow_count_augment_candidate_bound {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (path : List (Fin n)) :
    flowWorkTotal (flowCountAugmentCandidate C F s t path).2 ≤ 32 * (path.length + 1) ^ 2 := by
  have hn := flow_count_nodup_bound path
  have hp := flow_count_positive_residuals_bound C F s path.tail
  have hh : flowWorkTotal (flowCountHeadCheck s path).2 ≤ 3 := by
    cases path <;> simp only [flowCountHeadCheck, flowWorkTotal] <;> omega
  have hl : flowWorkTotal (flowCountLastCheck t path).2 ≤ 3 * path.length + 4 := by
    cases path with
    | nil => simp only [flowCountLastCheck, flowWorkTotal, List.length_nil]; omega
    | cons a tail =>
      have ht := flow_count_getLast_total a tail
      change flowWorkTotal (flowWorkAdd _ (flowCountGetLast a tail).2) ≤ _
      rw [flow_work_total_add, ht]
      change 3 + (3 * tail.length + 2) ≤ _
      simp only [List.length_cons]
      omega
  have htail : path.tail.length ≤ path.length := by cases path <;> simp
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ _)))) ≤ _
  repeat rw [flow_work_total_add]
  change flowWorkTotal (flowCountHeadCheck s path).2 +
    (flowWorkTotal (flowCountLastCheck t path).2 +
      (flowWorkTotal (flowCountNodup path).2 +
        (flowWorkTotal (flowCountPositiveResiduals C F s path.tail).2 + 3))) ≤ _
  nlinarith

end SparseCompletion
