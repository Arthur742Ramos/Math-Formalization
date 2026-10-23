/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.Quantization

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def activePrefix {m : ℕ} (q : Fin m → ℝ) (l : ℕ) : Finset (Fin m) := by
  classical
  exact (prefixSet l).filter fun j => q j ≠ 0

def residualSupport {m : ℕ} (q : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j => q j ≠ 0

def supportSize {m : ℕ} (q : Fin m → ℝ) : ℕ := (residualSupport q).card

theorem activePrefix_subset {m : ℕ} (q : Fin m → ℝ) (l : ℕ) :
    activePrefix q l ⊆ residualSupport q := by
  classical
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩

theorem activePrefix_mono {m : ℕ} (q : Fin m → ℝ) (l n : ℕ) (hln : l ≤ n) :
    activePrefix q l ⊆ activePrefix q n := by
  classical
  intro j hj
  obtain ⟨hjl,hq⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j,
    lt_of_lt_of_le (Finset.mem_filter.mp hjl).2 hln⟩,hq⟩

theorem prefixMass_active_sum {m : ℕ} (q : Fin m → ℝ) (l : ℕ) :
    prefixMass q l = ∑ j ∈ activePrefix q l, q j := by
  classical
  unfold prefixMass mass activePrefix
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hn
  by_contra hq
  exact hn (Finset.mem_filter.mpr ⟨hj,hq⟩)

theorem equal_active_card_prefixMass {m : ℕ} (q : Fin m → ℝ) (l n : ℕ)
    (hcard : (activePrefix q l).card = (activePrefix q n).card) :
    prefixMass q l = prefixMass q n := by
  rcases le_total l n with hln | hnl
  · have heq := Finset.eq_of_subset_of_card_le (activePrefix_mono q l n hln) (le_of_eq hcard.symm)
    rw [prefixMass_active_sum, prefixMass_active_sum, heq]
  · have heq := Finset.eq_of_subset_of_card_le (activePrefix_mono q n l hnl) (le_of_eq hcard)
    rw [prefixMass_active_sum, prefixMass_active_sum, heq]

def runLabel {m : ℕ} (q : Fin m → ℝ) (l : ℕ) : Fin (supportSize q+1) :=
  ⟨(activePrefix q l).card, Nat.lt_succ_of_le (Finset.card_le_card (activePrefix_subset q l))⟩

def runSet {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (a : Fin (supportSize q+1)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun l => runLabel q l.val=a

def runValue {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (a : Fin (supportSize q+1)) : ℝ := by
  classical
  exact if hs : (runSet q n a).Nonempty then prefixMass q ((runSet q n a).min' hs).val else 0

theorem prefixMass_on_run {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (a : Fin (supportSize q+1))
    (l : Fin n) (hl : l ∈ runSet q n a) : prefixMass q l.val = runValue q n a := by
  classical
  have hs : (runSet q n a).Nonempty := ⟨l,hl⟩
  unfold runValue
  rw [dite_eq_left hs]
  apply equal_active_card_prefixMass
  have hmin := Finset.min'_mem (runSet q n a) hs
  have hh : runLabel q l.val = runLabel q ((runSet q n a).min' hs).val :=
    (Finset.mem_filter.mp hl).2.trans (Finset.mem_filter.mp hmin).2.symm
  exact congrArg Fin.val hh

theorem run_card_sum {m : ℕ} (q : Fin m → ℝ) (n : ℕ) :
    (∑ a : Fin (supportSize q+1), ((runSet q n a).card : ℝ)) = n := by
  classical
  have hh := Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) (fun l => runLabel q l.val) (fun _ => (1 : ℝ))
  simpa only [runSet, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] using hh

theorem run_error_sum {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (d : ℝ) :
    (∑ l : Fin n, (prefixMass q l.val-d*(l.val : ℝ))^2) =
      ∑ a : Fin (supportSize q+1), ∑ l ∈ runSet q n a,
        (runValue q n a-d*(l.val : ℝ))^2 := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun l : Fin n => runLabel q l.val)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l hl
  rw [prefixMass_on_run q n a l hl]

/-- Quantization error for sparse cumulative mass. The candidate weights
    may even have arbitrary signs; only the number of nonzero entries matters. -/
theorem sparse_cumulative_quantization {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (d : ℝ) :
    d^2/12*((n : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2-(n : ℝ)) ≤
      ∑ l : Fin n, (prefixMass q l.val-d*(l.val : ℝ))^2 := by
  classical
  let L : Fin (supportSize q+1) → ℝ := fun a => (runSet q n a).card
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hJ := cubic_run_bound L (fun a => Nat.cast_nonneg _)
  have htotal : (∑ a, L a) = (n : ℝ) := run_card_sum q n
  rw [htotal] at hJ
  simp only [Fintype.card_fin] at hJ
  have hdiv : (n : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2 ≤ ∑ a, (L a)^3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    calc
      _ ≤ ((supportSize q+1 : ℕ) : ℝ)^2*∑ a, (L a)^3 := hJ
      _ = _ := mul_comm _ _
  calc
    _ ≤ d^2/12*((∑ a, (L a)^3)-(n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hdiv _) (by positivity)
    _ = ∑ a : Fin (supportSize q+1), d^2*(L a)*((L a)^2-1)/12 := by
      rw [← htotal]
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ _ := by
      rw [run_error_sum q n d]
      apply Finset.sum_le_sum
      intro a _
      simpa only [zero_add, L] using finite_subset_quantization_bound (runSet q n a) 0 d (runValue q n a)

end
end SparseCompletion
