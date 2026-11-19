module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Counting weighted subsets with and without repetition
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

theorem weighted_subsets_marked (s : Finset α) (w : α → ℝ) (k : ℕ) :
    (k + 1 : ℝ) * (∑ t ∈ s.powersetCard (k + 1), ∏ x ∈ t, w x) =
      ∑ t ∈ s.powersetCard k, ((∏ x ∈ t, w x) * ∑ i ∈ s \ t, w i) := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ t ∈ s.powersetCard (k + 1), ∑ _ ∈ t, ∏ x ∈ t, w x := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp ht).2, Nat.cast_succ]
    _ = ∑ t ∈ s.powersetCard k, ∑ i ∈ s \ t, (∏ x ∈ t, w x) * w i := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      let remove : (_ : Finset α) × α → (_ : Finset α) × α := fun ti ↦
        ⟨ti.1.erase ti.2, ti.2⟩
      let insertBack : (_ : Finset α) × α → (_ : Finset α) × α := fun ti ↦
        ⟨insert ti.2 ti.1, ti.2⟩
      apply Finset.sum_nbij' remove insertBack
      · rintro ⟨t, i⟩ h
        obtain ⟨ht, hi⟩ := Finset.mem_sigma.mp h
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
        exact Finset.mem_sigma.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset _ _).trans hsub,
            by rw [Finset.card_erase_of_mem hi, hcard, Nat.add_sub_cancel]⟩,
            Finset.mem_sdiff.mpr ⟨hsub hi, Finset.notMem_erase _ _⟩⟩
      · rintro ⟨t, i⟩ h
        obtain ⟨ht, hi⟩ := Finset.mem_sigma.mp h
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
        obtain ⟨his, hit⟩ := Finset.mem_sdiff.mp hi
        exact Finset.mem_sigma.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset his hsub,
            by rw [Finset.card_insert_of_notMem hit, hcard]⟩, Finset.mem_insert_self _ _⟩
      · rintro ⟨t, i⟩ h
        simp only [remove, insertBack, Finset.insert_erase (Finset.mem_sigma.mp h).2]
      · rintro ⟨t, i⟩ h
        simp only [remove, insertBack, Finset.erase_insert
          (Finset.mem_sdiff.mp (Finset.mem_sigma.mp h).2).2]
      · rintro ⟨t, i⟩ h
        exact (Finset.prod_erase_mul t w (Finset.mem_sigma.mp h).2).symm
    _ = _ := by simp only [Finset.mul_sum]

/-- Allowing repeated entries in ordered samples bounds the weight of
unordered distinct samples by the corresponding power divided by the factorial. -/
theorem sum_powersetCard_prod_le (s : Finset α) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (k : ℕ) :
    (∑ t ∈ s.powersetCard k, ∏ x ∈ t, w x) ≤
      (∑ x ∈ s, w x) ^ k / (k.factorial : ℝ) := by
  have hwSum : 0 ≤ ∑ x ∈ s, w x := Finset.sum_nonneg hw
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ,
      mul_comm (k + 1 : ℝ) (k.factorial : ℝ), div_mul_eq_div_div]
    apply (le_div_iff₀ (by positivity : 0 < (k + 1 : ℝ))).mpr
    rw [mul_comm, weighted_subsets_marked]
    calc
      _ ≤ ∑ t ∈ s.powersetCard k, (∏ x ∈ t, w x) * ∑ i ∈ s, w i := by
        apply Finset.sum_le_sum
        intro t ht
        have ht' := (Finset.mem_powersetCard.mp ht).1
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i hi _ ↦ hw i hi))
          (Finset.prod_nonneg (fun x hx ↦ hw x (ht' hx)))
      _ = (∑ t ∈ s.powersetCard k, ∏ x ∈ t, w x) * ∑ i ∈ s, w i := by
        rw [Finset.sum_mul]
      _ ≤ ((∑ i ∈ s, w i) ^ k / (k.factorial : ℝ)) * ∑ i ∈ s, w i :=
        mul_le_mul_of_nonneg_right ih hwSum
      _ = _ := by rw [div_mul_eq_mul_div]

/-- Sum a bound that holds with a suitably chosen anchor in each subset. -/
theorem sum_le_anchored_subsets {β : Type*} [Fintype β] [DecidableEq β]
    (k : ℕ) (f : Finset β → ℝ) (w : β → β → ℝ)
    (hw : ∀ v i, 0 ≤ w v i) (hdiag : ∀ v, w v v = 1)
    (hf : ∀ S : Finset β, S.card = k → ∃ v ∈ S, f S ≤ ∏ i ∈ S, w v i) :
    (∑ S : {S : Finset β // S.card = k}, f S.val) ≤
      ∑ v : β, (∑ i : β, w v i) ^ (k - 1) / ((k - 1).factorial : ℝ) := by
  classical
  let T := {S : Finset β // S.card = k}
  choose v hmem hbound using fun S : T ↦ hf S.val S.property
  let g (S : T) : Σ _ : β, Finset β := ⟨v S, S.val.erase (v S)⟩
  let R (v : β) := ((Finset.univ : Finset β).erase v).powersetCard (k - 1)
  have hg : Function.Injective g := by
    intro S U h
    apply Subtype.ext
    have hv : v S = v U := congrArg Sigma.fst h
    have hdel : S.val.erase (v S) = U.val.erase (v U) :=
      congrArg (fun t : Σ _ : β, Finset β ↦ t.2) h
    calc
      S.val = insert (v S) (S.val.erase (v S)) := (Finset.insert_erase (hmem S)).symm
      _ = insert (v U) (U.val.erase (v U)) := congrArg₂ insert hv hdel
      _ = U.val := Finset.insert_erase (hmem U)
  have hR (S : T) : g S ∈ Finset.univ.sigma R := by
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro i hi
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hi, Finset.mem_univ _⟩
    · rw [Finset.card_erase_of_mem (hmem S), S.property]
  calc
    _ ≤ ∑ t ∈ Finset.univ.sigma R, ∏ i ∈ t.2, w t.1 i := by
      refine Finset.sum_le_sum_of_injOn g hg.injOn ?_ ?_ ?_
      · intro t ht
        obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp ht
        exact hR S
      · intro S _
        change f S.val ≤ ∏ i ∈ S.val.erase (v S), w (v S) i
        simpa only [hdiag, mul_one] using
          (hbound S).trans_eq (Finset.prod_erase_mul S.val (w (v S)) (hmem S)).symm
      · intro t _ _
        exact Finset.prod_nonneg (fun i _ ↦ hw t.1 i)
    _ = ∑ v : β, ∑ t ∈ R v, ∏ i ∈ t, w v i := Finset.sum_sigma _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      refine (sum_powersetCard_prod_le _ _ (fun i _ ↦ hw v i) _).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ ↦ hw v i))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hw v i)


end BoundedEdgeRegularSubgraphs
