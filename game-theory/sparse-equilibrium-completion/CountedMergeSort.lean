/- AI-assisted formalization under the repository Apache-2.0 license.
Balanced sort with an intrinsic comparator-call ledger; no machine-cost claim. -/
module
public import CountedMerge
@[expose] public section
namespace SparseCompletion

def countedMergeSort {α : Type*} (le : α → α → Bool) : List α → List α × ℕ
  | [] => ([],0)
  | [a] => ([a],0)
  | a::b::xs =>
    let ys := a::b::xs
    let halves := ys.splitAt ((ys.length+1)/2)
    let left := countedMergeSort le halves.1
    let right := countedMergeSort le halves.2
    let merged := countedMerge le left.1 right.1
    (merged.1,left.2+right.2+merged.2)
termination_by xs => xs.length
decreasing_by
  · change Nat.lt
      ((List.splitAt (((a::b::xs).length+1)/2) (a::b::xs)).1.length)
      (a::b::xs).length
    rw [List.splitAt_eq, List.length_take]
    have hh : Nat.lt (Nat.add (Nat.add xs.length 2) 1)
        (Nat.mul (Nat.add xs.length 2) 2) := by
      have hm : Nat.mul (Nat.add xs.length 2) 2 =
          Nat.add (Nat.add xs.length 2) (Nat.add xs.length 2) :=
        Nat.mul_two (Nat.add xs.length 2)
      rw [hm]
      exact Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.zero_lt_succ xs.length)) _
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _)
      ((Nat.div_lt_iff_lt_mul Nat.zero_lt_two).2 hh)
  · change Nat.lt
      ((List.splitAt (((a::b::xs).length+1)/2) (a::b::xs)).2.length)
      (a::b::xs).length
    rw [List.splitAt_eq, List.length_drop]
    apply Nat.sub_lt (Nat.succ_pos _)
    exact Nat.div_pos
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le (xs.length+1)))) Nat.zero_lt_two

theorem counted_merge_sort_length {α : Type*} (le : α → α → Bool) (xs : List α) :
    (countedMergeSort le xs).1.length=xs.length := by
  fun_induction countedMergeSort le xs
  all_goals simp_all +zetaDelta [counted_merge_length,List.splitAt_eq]
  all_goals omega


theorem counted_sort_half_lengths {α : Type*} (xs : List α) :
    (xs.splitAt ((xs.length+1)/2)).1.length=(xs.length+1)/2 ∧
    (xs.splitAt ((xs.length+1)/2)).2.length=xs.length/2 := by
  simp only [List.splitAt_eq,List.length_take,List.length_drop]
  omega

theorem counted_merge_sort_capacity {α : Type*} (le : α → α → Bool)
    (xs : List α) (h : ℕ) (hcap : xs.length ≤ Nat.pow 2 h) :
    (countedMergeSort le xs).2 ≤ xs.length*h := by
  induction h generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [countedMergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp [countedMergeSort]
      | cons b xs =>
        have hh : (a::b::xs).length ≤ 1 := hcap
        simp only [List.length_cons] at hh
        omega
  | succ h ih =>
    cases xs with
    | nil => simp [countedMergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp [countedMergeSort]
      | cons b xs =>
        let ys := a::b::xs
        let halves := ys.splitAt ((ys.length+1)/2)
        have hparts := counted_sort_half_lengths ys
        have hl : halves.1.length=(ys.length+1)/2 := hparts.1
        have hr : halves.2.length=ys.length/2 := hparts.2
        have hn : ys.length ≤ Nat.pow 2 h*2 := hcap
        have hleft : halves.1.length ≤ Nat.pow 2 h := by rw [hl]; omega
        have hright : halves.2.length ≤ Nat.pow 2 h := by rw [hr]; omega
        have hsum : halves.1.length+halves.2.length=ys.length := by rw [hl,hr]; omega
        have hcL := ih halves.1 hleft
        have hcR := ih halves.2 hright
        have hcM := counted_merge_bound le (countedMergeSort le halves.1).1
          (countedMergeSort le halves.2).1
        rw [counted_merge_sort_length,counted_merge_sort_length] at hcM
        rw [countedMergeSort]
        change (countedMergeSort le halves.1).2+(countedMergeSort le halves.2).2+
            (countedMerge le (countedMergeSort le halves.1).1
              (countedMergeSort le halves.2).1).2 ≤ ys.length*(h+1)
        calc
          _ ≤ halves.1.length*h+halves.2.length*h+
              (halves.1.length+halves.2.length) := Nat.add_le_add (Nat.add_le_add hcL hcR) hcM
          _ = (halves.1.length+halves.2.length)*(h+1) := by simp only [Nat.mul_succ,Nat.add_mul]
          _ = ys.length*(h+1) := by rw [hsum]

theorem counted_merge_sort_log_bound {α : Type*} (le : α → α → Bool) (xs : List α) :
    (countedMergeSort le xs).2 ≤ xs.length*(Nat.log2 xs.length+1) := by
  exact counted_merge_sort_capacity le xs _ (Nat.le_of_lt Nat.lt_log2_self)


theorem counted_merge_sort_perm {α : Type*} (le : α → α → Bool) (xs : List α) :
    (countedMergeSort le xs).1.Perm xs := by
  fun_induction countedMergeSort le xs
  all_goals simp_all +zetaDelta [counted_merge_value,List.splitAt_eq]
  apply (List.merge_perm_append le).trans
  apply List.Perm.trans
  · apply List.Perm.append
    all_goals assumption
  · exact List.Perm.of_eq (List.take_append_drop _ _)

theorem counted_merge_sort_pairwise {α : Type*} (le : α → α → Bool)
    (trans : ∀ a b c,le a b → le b c → le a c)
    (total : ∀ a b,le a b = true ∨ le b a = true) (xs : List α) :
    (countedMergeSort le xs).1.Pairwise (fun a b => le a b = true) := by
  fun_induction countedMergeSort le xs
  all_goals simp_all +zetaDelta [counted_merge_value]
  apply List.pairwise_merge trans (fun a b => by simpa only [Bool.or_eq_true] using total a b)
  all_goals assumption

end SparseCompletion
