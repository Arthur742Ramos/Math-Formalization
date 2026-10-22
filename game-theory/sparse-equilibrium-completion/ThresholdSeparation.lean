/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import IntervalConic
public import ScorePrefixes

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def positiveScoreSet {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => q i ≠ 0 ∧ 0 < v i-z

def weightedUpperSet {ι : Type*} [Fintype ι] (q v : ι → ℝ) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun j => q j ≠ 0 ∧ v i ≤ v j

theorem positive_score_threshold {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ)
    (hs : (positiveScoreSet q v z).Nonempty) :
    ∃ i, q i ≠ 0 ∧ positiveScoreSet q v z=weightedUpperSet q v i := by
  classical
  let s := positiveScoreSet q v z
  obtain ⟨i,hi,hmin⟩ := Set.exists_min_image (s : Set ι) v s.finite_toSet hs
  have hip := (Finset.mem_filter.mp hi).2
  refine ⟨i,hip.1,?_⟩
  ext j
  simp only [positiveScoreSet,weightedUpperSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hq,hv⟩
    exact ⟨hq,hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hv⟩)⟩
  · rintro ⟨hq,hv⟩
    exact ⟨hq,by linarith [hip.2]⟩

theorem positive_score_call_identity {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ) :
    call q v z=(∑ i ∈ positiveScoreSet q v z, q i*v i)-z*mass (positiveScoreSet q v z) q := by
  classical
  have hh : call q v z=∑ i ∈ positiveScoreSet q v z, q i*(v i-z) := by
    unfold call positiveScoreSet
    rw [←Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i => q i ≠ 0 ∧ 0 < v i-z)]
    have hz : (∑ i ∈ Finset.univ.filter (fun i => ¬(q i ≠ 0 ∧ 0 < v i-z)),
        q i*max (v i-z) 0)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hn := (Finset.mem_filter.mp hi).2
      by_cases hq : q i=0
      · rw [hq,zero_mul]
      · have hv : ¬0 < v i-z := fun hv => hn ⟨hq,hv⟩
        rw [max_eq_right (le_of_not_gt hv),mul_zero]
    rw [hz,add_zero]
    exact Finset.sum_congr rfl fun i hi => by
      rw [max_eq_left (le_of_lt (Finset.mem_filter.mp hi).2.2)]
  rw [hh]
  simp only [mass,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  simp only [mul_comm]

theorem cuts_iff_positive_thresholds {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i=r) :
    Cuts M r q v ↔ ∀ i, q i ≠ 0 →
      (∑ j ∈ weightedUpperSet q v i, q j*v j) ≤
        M*mass (weightedUpperSet q v i) q*(r-mass (weightedUpperSet q v i) q) := by
  constructor
  · intro h i _
    exact h _
  · intro hp
    apply call_bound_implies_cuts q v M r hM hq hmass
    intro z _
    classical
    let s := positiveScoreSet q v z
    let Q := mass s q
    have hc : (∑ i ∈ s, q i*v i) ≤ M*Q*(r-Q) := by
      by_cases hs : s.Nonempty
      · obtain ⟨i,hi,he⟩ := positive_score_threshold q v z hs
        dsimp only [Q,s]
        rw [he]
        exact hp i hi
      · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        dsimp only [Q]
        simp only [he,mass,Finset.sum_empty,mul_zero,zero_mul,sub_zero,le_refl]
    have hsq := sq_nonneg ((2 : ℕ)*M*Q-(M*r-z))
    have he : (4 : ℕ)*M*envelope M r z=(M*r-z)^2 := by
      unfold envelope
      norm_num only [Nat.cast_ofNat]
      field_simp
    rw [positive_score_call_identity]
    apply (mul_le_mul_iff_right₀ (show 0 < (4 : ℕ)*M by positivity)).mp
    dsimp only [Q,s] at hc hsq
    rw [he]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith

def effectiveScore {ι : Type*} (q H : ι → ℝ) (i : ι) : ℝ :=
  if q i=0 then 0 else H i/q i

theorem effective_score_product {ι : Type*} (q H : ι → ℝ)
    (hzero : ∀ i, q i=0 → H i=0) (i : ι) : q i*effectiveScore q H i=H i := by
  unfold effectiveScore
  split_ifs with h
  · rw [hzero i h,mul_zero]
  · field_simp

theorem perspective_cuts_iff_candidate_thresholds {ι : Type*} [Fintype ι]
    (q H : ι → ℝ) (M r ε : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i=r) (hzero : ∀ i, q i=0 → H i=0) :
    perspectiveCuts q H M r ε ↔ ∀ i : ι, q i ≠ 0 →
      M*(mass (weightedUpperSet q (effectiveScore q H) i) q)^2-
        M*r*mass (weightedUpperSet q (effectiveScore q H) i) q+
        (∑ j ∈ (weightedUpperSet q (effectiveScore q H) i : Finset ι), (H j-ε*q j : ℝ)) ≤ 0 := by
  have hprod := effective_score_product q H hzero
  rw [←perspective_cuts_iff q (effectiveScore q H) H M r ε hprod,
    cuts_iff_positive_thresholds q (fun i : ι => effectiveScore q H i-ε) M r hM hq hmass]
  have he : ∀ i, weightedUpperSet q (fun j : ι => effectiveScore q H j-ε) i=
      weightedUpperSet q (effectiveScore q H) i := by
    intro i
    classical
    ext j
    simp only [weightedUpperSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_congr_right fun _ => sub_le_sub_iff_right ε
  simp_rw [he]
  have hs : ∀ S : Finset ι, (∑ j ∈ S, q j*(effectiveScore q H j-ε))=
      ∑ j ∈ S, (H j-ε*q j) := by
    intro S
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_sub,hprod j,mul_comm (q j) ε]
  simp_rw [hs]
  constructor <;> intro h i hi <;> have hc := h i hi <;> nlinarith

end
end SparseCompletion
