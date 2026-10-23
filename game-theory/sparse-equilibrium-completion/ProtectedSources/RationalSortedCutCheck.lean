/- AI-assisted formalization under the repository Apache-2.0 license.
Sort and early-exit scan share one returned comparison ledger. Arithmetic,
getter work and bit costs are outside this comparison-count statement. -/
module
public import ProtectedSources.ListPrefixSum
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSortedCutCheck {m : ℕ} (M r δ : ℚ) (q f : Fin m → ℚ) : Bool × ℕ :=
  let sorted := rationalLabelSort f
  let scan := rationalPrefixScan M r δ 0 0
    (sorted.1.map (fun a => (q a.1, q a.1*a.2)))
  (scan.1, sorted.2+scan.2)

theorem rational_sorted_cut_check_comparisons {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedCutCheck M r δ q f).2 ≤ m*(Nat.log2 m+2)+1 := by
  have hs := rational_label_sort_comparisons f
  have hp := rational_prefix_scan_comparisons M r δ 0 0
    ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2)))
  simp only [List.length_map, rational_label_sort_length] at hp
  change (rationalLabelSort f).2+
    (rationalPrefixScan M r δ 0 0
      ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2)))).2 ≤ _
  calc
    _ ≤ m*(Nat.log2 m+1)+(m+1) := Nat.add_le_add hs hp
    _ = m*(Nat.log2 m+2)+1 := by simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]; omega

theorem rational_sorted_cut_check_prefix_iff {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedCutCheck M r δ q f).1 = true ↔
      ∀ l : ℕ, l ≤ (rationalLabelSort f).1.length →
        (∑ i ∈ scorePrefix (rationalLabelSort f).1.length l,
            q (rationalSortedIndex f i)*f (rationalSortedIndex f i))-
          M*(∑ i ∈ scorePrefix (rationalLabelSort f).1.length l,
            q (rationalSortedIndex f i))*
            (r-∑ i ∈ scorePrefix (rationalLabelSort f).1.length l,
              q (rationalSortedIndex f i)) ≤ δ := by
  change (rationalPrefixScan M r δ 0 0
    ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2)))).1 = true ↔ _
  rw [rational_prefix_scan_complete]
  simp only [List.length_map, ← List.map_take, List.map_map, Function.comp_def, zero_add]
  simp_rw [list_take_sum_scorePrefix, rational_sorted_index_score]
  rfl

theorem rational_sorted_cut_check_iff {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) :
    (rationalSortedCutCheck M r δ q f).1 = true ↔
      ∀ S : Finset (Fin m),
        (∑ i ∈ S, (q i : ℝ)*(f i : ℝ))-
          (M : ℝ)*mass S (fun i => (q i : ℝ))*
            ((r : ℝ)-mass S (fun i => (q i : ℝ))) ≤ (δ : ℝ) := by
  rw [rational_sorted_cut_check_prefix_iff]
  have hMr : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hqr : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := by intro i; exact_mod_cast hq i
  have hreal := rational_sorted_cut_prefix_criterion (fun i => (q i : ℝ)) f
    (M : ℝ) (r : ℝ) (δ : ℝ) hMr hqr
  constructor
  · intro hp
    apply hreal.mpr
    intro l hl
    have hh := hp l hl
    dsimp only [mass]
    exact_mod_cast hh
  · intro hall l hl
    have hh := hreal.mp hall l hl
    dsimp only [mass] at hh
    exact_mod_cast hh

end SparseCompletion
