/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalFloorSparseValue
public import ProtectedSources.RationalGridSizeBounds
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_floor_sparse_total_support {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSparseApproximation d s hs ε=some v) :
    (Finset.univ.filter fun a =>
      blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ)) a ≠ 0).card ≤
      min (k+m) ((2 : ℕ)*k+rationalGridSize d.M (1-∑ a,v.1 a) (ε/((2 : ℕ) : ℚ))+1) := by
  obtain ⟨_,w,_,hv⟩ := rational_floor_sparse_origin d s hs ε v hout
  obtain ⟨hp,_,_,_,ha⟩ := rational_floor_sparsify_origin d (ε/((2 : ℕ) : ℚ)) w v hv
  have hc := rational_sparse_gap_algorithm_full_support w.2.K w.2.D w.1 d.M (1-∑ a,w.1 a)
    (w.2.bracket.2+(ε/((2 : ℕ) : ℚ))/((3 : ℕ) : ℚ)) (ε/((2 : ℕ) : ℚ))
    (rationalUnconstrainedSystem m) v.2.q v.2.B ha
  simpa only [hp,Fintype.card_fin,Nat.add_zero] using hc

theorem rational_floor_sparse_sqrt_support {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (ε : ℚ)
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSparseApproximation d s hs ε=some v) :
    ((Finset.univ.filter fun a =>
      blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ)) a ≠ 0).card : ℝ) ≤
      ((2 : ℕ) : ℝ)*(k : ℝ)+Real.sqrt (((2 : ℕ) : ℝ)*(d.M : ℝ)/(ε : ℝ))+(3 : ℕ) := by
  have hε := (rational_floor_sparse_origin d s hs ε v hout).1
  have he : (0 : ℚ) < ε/((2 : ℕ) : ℚ) := div_pos hε (by norm_num)
  have heR : (0 : ℝ) < ((ε/((2 : ℕ) : ℚ) : ℚ) : ℝ) := by exact_mod_cast he
  have hclass := (rational_floor_sparse_output_game d s hs hR ε v hout).1
  rcases hclass with ⟨⟨hp,hq,_,_,_,_⟩,_,_,hmass,_⟩
  have hp0 : 0 ≤ ∑ a,(v.1 a : ℝ) := Finset.sum_nonneg fun a _ => hp.1 a
  have hq0 : 0 ≤ ∑ i,(v.2.q i : ℝ) := Finset.sum_nonneg fun i _ => hq.1 i
  change (∑ a,(v.1 a : ℝ))+(∑ i,(v.2.q i : ℝ))=1 at hmass
  have hr0 : (0 : ℚ) ≤ 1-∑ a,v.1 a := by
    have hh : (0 : ℝ) ≤ ((1-∑ a,v.1 a : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast hh
  have hr1 : ((1-∑ a,v.1 a : ℚ) : ℝ) ≤ 1 := by push_cast; linarith
  have hM : (0 : ℝ) ≤ (d.M : ℝ) := by exact_mod_cast d.positiveBound.le
  have hratio : (d.M : ℝ)*((1-∑ a,v.1 a : ℚ) : ℝ)/((ε/((2 : ℕ) : ℚ) : ℚ) : ℝ) ≤
      ((2 : ℕ) : ℝ)*(d.M : ℝ)/(ε : ℝ) := by
    calc
      _ ≤ (d.M : ℝ)/((ε/((2 : ℕ) : ℚ) : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_right hM hr1) heR.le
      _ = _ := by push_cast; ring
  have hH := rational_grid_size_sqrt_bound d.M (1-∑ a,v.1 a) (ε/((2 : ℕ) : ℚ))
    d.positiveBound.le hr0 he
  have hH' := add_le_add_left (Real.sqrt_le_sqrt hratio) ((2 : ℕ) : ℝ)
  have hH' := le_trans hH hH'
  have hc := le_trans (rational_floor_sparse_total_support d s hs ε v hout) (min_le_right _ _)
  have hcR : ((Finset.univ.filter fun a =>
      blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ)) a ≠ 0).card : ℝ) ≤
      ((2 : ℕ) : ℝ)*(k : ℝ)+(rationalGridSize d.M (1-∑ a,v.1 a) (ε/((2 : ℕ) : ℚ)) : ℝ)+1 := by
    exact_mod_cast hc
  norm_num only [Nat.cast_ofNat] at hH' hcR ⊢
  linarith

end SparseCompletion
