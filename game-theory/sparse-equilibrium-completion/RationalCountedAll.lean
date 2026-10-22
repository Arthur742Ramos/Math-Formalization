/- AI-assisted formalization under the repository Apache-2.0 license.
Counter counts all generated tests; actual Boolean short-circuit savings are unused. -/
module
public import RationalCountedDot
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCountedConjunction : List (Bool × ℕ) → Bool × ℕ
  | [] => (true,0)
  | x::xs =>
    let z := rationalCountedConjunction xs
    (x.1 && z.1,x.2+z.2)

theorem rational_counted_conjunction_value (xs : List (Bool × ℕ)) :
    (rationalCountedConjunction xs).1=true ↔ ∀ x ∈ xs,x.1=true := by
  induction xs with
  | nil => simp only [rationalCountedConjunction,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons x xs ih =>
    simp only [rationalCountedConjunction,Bool.and_eq_true,ih,List.mem_cons,forall_eq_or_imp]

theorem rational_counted_conjunction_calls (xs : List (Bool × ℕ)) :
    (rationalCountedConjunction xs).2=(xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [rationalCountedConjunction,List.map_cons,List.sum_cons,ih]

def rationalCountedAll {n : ℕ} (f : Fin n → Bool × ℕ) : Bool × ℕ :=
  rationalCountedConjunction (List.ofFn f)

theorem rational_counted_all_value {n : ℕ} (f : Fin n → Bool × ℕ) :
    (rationalCountedAll f).1=true ↔ ∀ i,(f i).1=true := by
  rw [rationalCountedAll,rational_counted_conjunction_value]
  simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]

theorem rational_counted_all_calls {n : ℕ} (f : Fin n → Bool × ℕ) :
    (rationalCountedAll f).2=∑ i,(f i).2 := by
  rw [rationalCountedAll,rational_counted_conjunction_calls,List.map_ofFn]
  exact Fin.sum_ofFn _

end SparseCompletion
