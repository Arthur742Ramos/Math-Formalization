/- AI-assisted formalization under the repository Apache-2.0 license.
Explicit unit arithmetic-call ledger; no machine runtime or bit-cost assertion. -/
module
public import ProtectedSources.RationalCertificate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCountedDot : List (ℚ × ℚ) → ℚ × ℕ
  | [] => (0,0)
  | (a,b)::xs =>
    let z := rationalCountedDot xs
    (a*b+z.1,z.2+((2 : ℕ)))

theorem rational_counted_dot_value (xs : List (ℚ × ℚ)) :
    (rationalCountedDot xs).1=(xs.map fun z => z.1*z.2).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [rationalCountedDot,List.map_cons,List.sum_cons,ih]

theorem rational_counted_dot_calls (xs : List (ℚ × ℚ)) :
    (rationalCountedDot xs).2=((2 : ℕ))*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [rationalCountedDot,List.length_cons,ih]; omega

def rationalCountedFinDot {n : ℕ} (f g : Fin n → ℚ) : ℚ × ℕ :=
  rationalCountedDot (List.ofFn fun i => (f i,g i))

theorem rational_counted_fin_dot_value {n : ℕ} (f g : Fin n → ℚ) :
    (rationalCountedFinDot f g).1=∑ i,f i*g i := by
  rw [rationalCountedFinDot,rational_counted_dot_value,List.map_ofFn]
  exact Fin.sum_ofFn _

theorem rational_counted_fin_dot_calls {n : ℕ} (f g : Fin n → ℚ) :
    (rationalCountedFinDot f g).2=((2 : ℕ))*n := by
  simp only [rationalCountedFinDot,rational_counted_dot_calls,List.length_ofFn]

end SparseCompletion
