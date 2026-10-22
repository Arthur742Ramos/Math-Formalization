/- AI-assisted formalization under the repository Apache-2.0 license.
Actual sorted cut program with comparison and source rational arithmetic ledgers.
The supplied score function is materialized by the existing label sort; the
score/getter computation, rational normalization, bit sizes and allocation are
outside this ledger. The arithmetic charge includes one weighted-score product
per materialized table entry and the intrinsic cached scan's operations. -/
module
public import RationalPrefixArithmetic
public import RationalSortedCutCheck
@[expose] public section
namespace SparseCompletion

def rationalSortedArithmetic {m : ℕ} (M r δ : ℚ) (q f : Fin m → ℚ) :
    Bool × ℕ × ℕ :=
  let sorted := rationalLabelSort f
  let scan := rationalPrefixArithmetic M r δ 0 0
    (sorted.1.map (fun a => (q a.1,q a.1*a.2)))
  (scan.1,sorted.2+scan.2.1,sorted.1.length+scan.2.2)

theorem rational_sorted_arithmetic_projection {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    ((rationalSortedArithmetic M r δ q f).1,
      (rationalSortedArithmetic M r δ q f).2.1) =
      rationalSortedCutCheck M r δ q f := by
  have hh := rational_prefix_arithmetic_projection M r δ 0 0
    ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2)))
  exact congrArg (fun out : Bool × ℕ =>
    (out.1,(rationalLabelSort f).2+out.2)) hh

theorem rational_sorted_arithmetic_comparisons {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedArithmetic M r δ q f).2.1 ≤ m*(Nat.log2 m+2)+1 := by
  have hh := congrArg Prod.snd (rational_sorted_arithmetic_projection M r δ q f)
  change (rationalSortedArithmetic M r δ q f).2.1 =
    (rationalSortedCutCheck M r δ q f).2 at hh
  rw [hh]
  exact rational_sorted_cut_check_comparisons M r δ q f

theorem rational_sorted_arithmetic_operations {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedArithmetic M r δ q f).2.2 ≤ 7*m+4 := by
  have hh := rational_prefix_arithmetic_operations M r δ 0 0
    ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2)))
  simp only [List.length_map,rational_label_sort_length] at hh
  change (rationalLabelSort f).1.length +
    (rationalPrefixArithmetic M r δ 0 0
      ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2)))).2.2 ≤ _
  rw [rational_label_sort_length]
  omega

theorem rational_sorted_arithmetic_combined {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedArithmetic M r δ q f).2.1+
      (rationalSortedArithmetic M r δ q f).2.2 ≤ m*(Nat.log2 m+9)+5 := by
  have hc := rational_sorted_arithmetic_comparisons M r δ q f
  have ha := rational_sorted_arithmetic_operations M r δ q f
  calc
    _ ≤ (m*(Nat.log2 m+2)+1)+(7*m+4) := Nat.add_le_add hc ha
    _ = _ := by simp only [Nat.mul_add]; omega

end SparseCompletion
