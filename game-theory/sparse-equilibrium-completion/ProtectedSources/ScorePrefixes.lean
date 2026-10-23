/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.CompletionCriterion

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def scorePrefix (m l : ℕ) : Finset (Fin m) := Finset.univ.filter fun i => i.val<l

theorem threshold_is_score_prefix {m : ℕ} (v : Fin m → ℝ) (hv : Antitone v) (z : ℝ) :
    ∃ l : ℕ, l ≤ m ∧ (Finset.univ.filter fun i => 0 < v i-z)=scorePrefix m l := by
  classical
  let s := Finset.univ.filter fun i => 0 < v i-z
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hjv : 0 < v j-z := (Finset.mem_filter.mp hj).2
    refine ⟨j.val+1,by omega,?_⟩
    ext i
    change i ∈ s ↔ i ∈ scorePrefix m (j.val+1)
    simp only [scorePrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hi
      have hle : i ≤ j := Finset.le_max' s i hi
      exact Nat.lt_succ_iff.mpr (show i.val ≤ j.val from hle)
    · intro hi
      have hle : i ≤ j := show i.val ≤ j.val from Nat.lt_succ_iff.mp hi
      have hvi := hv hle
      change i ∈ Finset.univ.filter fun i => 0 < v i-z
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith⟩
  · refine ⟨0,Nat.zero_le _,?_⟩
    have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa only [scorePrefix,Nat.not_lt_zero,Finset.filter_false] using he

theorem cuts_iff_score_prefixes {m : ℕ} (q v : Fin m → ℝ) (M r : ℝ)
    (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i=r) (hv : Antitone v) :
    Cuts M r q v ↔ ∀ l : ℕ, l ≤ m →
      (∑ i ∈ scorePrefix m l, q i*v i) ≤
        M*mass (scorePrefix m l) q*(r-mass (scorePrefix m l) q) := by
  constructor
  · intro hc l _
    exact hc _
  · intro hp
    apply call_bound_implies_cuts q v M r hM hq hmass
    intro z _
    classical
    let s := Finset.univ.filter fun i => 0 < v i-z
    let Q := mass s q
    have heq : call q v z = (∑ i ∈ s, q i*v i)-z*Q := by
      have hh : call q v z = ∑ i ∈ s, q i*(v i-z) := by
        unfold call
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < v i-z)]
        have hz : (∑ i ∈ Finset.univ.filter (fun i => ¬0 < v i-z), q i*max (v i-z) 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have := (Finset.mem_filter.mp hi).2
          rw [max_eq_right (le_of_not_gt this), mul_zero]
        rw [hz, add_zero]
        exact Finset.sum_congr rfl fun i hi => by rw [max_eq_left (le_of_lt (Finset.mem_filter.mp hi).2)]
      rw [hh]
      simp only [Q, mass, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      simp only [mul_comm]
    obtain ⟨l,hl,he⟩ := threshold_is_score_prefix v hv z
    have hc : (∑ i ∈ s, q i*v i) ≤ M*Q*(r-Q) := by
      dsimp only [Q,s]
      rw [he]
      exact hp l hl
    have hs := sq_nonneg (2*M*Q - (M*r-z))
    have he : 4*M*envelope M r z = (M*r-z)^2 := by
      unfold envelope
      field_simp
    rw [heq]
    apply (mul_le_mul_iff_right₀ (show 0 < 4*M by positivity)).mp
    nlinarith

end
end SparseCompletion
