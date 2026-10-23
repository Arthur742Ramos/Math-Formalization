/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.PrefixStability
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Finset.Sort

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Exact discrete variance decomposition on an arithmetic progression. -/
theorem constant_run_error_identity (L : ℕ) (a d c : ℝ) :
    (∑ i ∈ Finset.range L, (c-(a+d*(i : ℝ)))^2) =
      (L : ℝ)*(c-a-d*((L : ℝ)-1)/2)^2+d^2*(L : ℝ)*((L : ℝ)^2-1)/12 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem constant_run_error_lower (L : ℕ) (a d c : ℝ) :
    d^2*(L : ℝ)*((L : ℝ)^2-1)/12 ≤ ∑ i ∈ Finset.range L, (c-(a+d*(i : ℝ)))^2 := by
  rw [constant_run_error_identity]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg L) (sq_nonneg _))

/-- Cubic run-length Jensen inequality with no positivity floor on runs. -/
theorem cubic_run_bound {κ : Type*} [Fintype κ] (L : κ → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (∑ i, L i)^3 ≤ (Fintype.card κ : ℝ)^2*∑ i, (L i)^3 := by
  simpa only [Finset.card_univ] using
    pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := L) (fun i _ => hL i) 2

theorem pairwise_square_sum {κ : Type*} [Fintype κ] (v : κ → ℝ) :
    (∑ i, ∑ j, (v i-v j)^2) =
      2*((Fintype.card κ : ℝ)*(∑ i, (v i)^2)-(∑ i, v i)^2) := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem first_index_moment (L : ℕ) :
    (∑ i ∈ Finset.range L, (i : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem pairwise_index_square_sum (L : ℕ) :
    (∑ i : Fin L, ∑ j : Fin L, ((i.val : ℝ)-(j.val : ℝ))^2) =
      (L : ℝ)^2*((L : ℝ)^2-1)/6 := by
  have hsum : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact first_index_moment L
  have hsq : (∑ i : Fin L, (i.val : ℝ)^2) =
      (L : ℝ)*(((L : ℝ)-1)/2)^2+(L : ℝ)*((L : ℝ)^2-1)/12 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)^2)]
    simpa only [zero_add, one_mul, zero_sub, neg_sq, one_pow, mul_one, sub_zero] using
      constant_run_error_identity L 0 1 0
  rw [pairwise_square_sum, Fintype.card_fin, hsum, hsq]
  ring

theorem increasing_nat_distance {L n : ℕ} (e : Fin L ↪o Fin n) (i j : Fin L) (hij : i ≤ j) :
    i.val+(e j).val ≥ j.val+(e i).val := by
  have hstep : ∀ k (hk : i.val+k < L), (e i).val+k ≤ (e ⟨i.val+k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; simpa only [Nat.add_zero] using le_rfl (a := (e i).val)
    | succ k ih =>
      intro hk
      have hk0 : i.val+k < L := by omega
      have hh := ih hk0
      have hlt : (e ⟨i.val+k,hk0⟩).val  <  (e ⟨i.val+(k+1),hk⟩).val :=
        e.strictMono (by change i.val+k < i.val+(k+1); omega)
      omega
  have hval : i.val ≤ j.val := hij
  have hbound : i.val+(j.val-i.val) < L := by omega
  have hh := hstep (j.val-i.val) hbound
  have hsame : (⟨i.val+(j.val-i.val),hbound⟩ : Fin L) = j := Fin.ext (by change i.val+(j.val-i.val)=j.val; omega)
  rw [hsame] at hh
  omega

theorem increasing_square_distance {L n : ℕ} (e : Fin L ↪o Fin n) (i j : Fin L) :
    ((i.val : ℝ)-(j.val : ℝ))^2 ≤ (((e i).val : ℝ)-((e j).val : ℝ))^2 := by
  rcases le_total i j with hij | hji
  · have hh := increasing_nat_distance e i j hij
    have hm : (e i).val ≤ (e j).val := e.monotone hij
    have hval : i.val ≤ j.val := hij
    have hc : (j.val : ℝ)+(e i).val ≤ (i.val : ℝ)+(e j).val := by exact_mod_cast hh
    have hc0 : (i.val : ℝ) ≤ j.val := by exact_mod_cast hval
    nlinarith
  · have hh := increasing_nat_distance e j i hji
    have hval : j.val ≤ i.val := hji
    have hc : (i.val : ℝ)+(e j).val ≤ (j.val : ℝ)+(e i).val := by exact_mod_cast hh
    have hc0 : (j.val : ℝ) ≤ i.val := by exact_mod_cast hval
    nlinarith

/-- Any L distinct integer grid points have at least the variance of L
    consecutive points. No contiguity or chosen run partition is assumed. -/
theorem finite_subset_quantization_bound {n : ℕ} (s : Finset (Fin n)) (a d c : ℝ) :
    d^2*(s.card : ℝ)*((s.card : ℝ)^2-1)/12 ≤
      ∑ j ∈ s, (c-(a+d*(j.val : ℝ)))^2 := by
  classical
  by_cases hs : s.card=0
  · have he : s=∅ := Finset.card_eq_zero.mp hs
    subst s
    simp
  · let L := s.card
    have hL : 0 < (L : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    let e : Fin L ↪o Fin n := s.orderEmbOfFin rfl
    let v : Fin L → ℝ := fun i => c-(a+d*((e i).val : ℝ))
    have hsum : (∑ j ∈ s, (c-(a+d*(j.val : ℝ)))^2) = ∑ i, (v i)^2 := by
      rw [← s.map_orderEmbOfFin_univ rfl, Finset.sum_map]
      rfl
    have hdifference : ∀ i j, (v i-v j)^2 = d^2*(((e i).val : ℝ)-((e j).val : ℝ))^2 := by
      intro i j
      dsimp [v]
      ring
    have hpair : d^2*((L : ℝ)^2*((L : ℝ)^2-1)/6) ≤ ∑ i, ∑ j, (v i-v j)^2 := by
      rw [← pairwise_index_square_sum L]
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [hdifference]
      exact mul_le_mul_of_nonneg_left (increasing_square_distance e i j) (sq_nonneg d)
    rw [pairwise_square_sum, Fintype.card_fin] at hpair
    rw [hsum]
    apply (mul_le_mul_iff_right₀ (show 0 < 2*(L : ℝ) by positivity)).mp
    have hsq := sq_nonneg (∑ i, v i)
    change 2*(L : ℝ)*(d^2*(L : ℝ)*((L : ℝ)^2-1)/12) ≤ 2*(L : ℝ)*∑ i, (v i)^2
    nlinarith

end
end SparseCompletion
