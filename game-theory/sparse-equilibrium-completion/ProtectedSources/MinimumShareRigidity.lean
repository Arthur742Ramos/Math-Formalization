/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.TwoAnchorRigidity

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem two_anchor_variable_responses {m : ℕ} (t w q : Fin m → ℝ)
    (a : Fin 2 → ℝ) (p βstar : ℝ) :
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) a q 0 =
      (2*βstar/p)*a 1-scoreMoment q t/p-scoreMoment q w ∧
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) a q 1 =
      -(2*βstar/p)*a 0-scoreMoment q t/p+scoreMoment q w := by
  have hsum : (∑ i, t i/p*q i) = scoreMoment q t/p := by
    unfold scoreMoment
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : (∑ i, w i*q i) = scoreMoment q w := by
    unfold scoreMoment
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor <;>
    simp only [anchorResponse, Fin.sum_univ_two, twoCore, twoCross] <;>
    norm_num <;>
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hw] <;>
    ring

theorem exposing_moment_positive {m : ℕ} (hm : 2 ≤ m) (qstar : Fin m → ℝ)
    (r : ℝ) (hpos : ∀ j, 0 < qstar j) (hr : ∑ j, qstar j = r) :
    0 < scoreMoment qstar (exposingWeight qstar r) := by
  let j : Fin m := ⟨0,by omega⟩
  have hn : ∀ i, 0 ≤ qstar i := fun i => le_of_lt (hpos i)
  have hw := exposingWeight_positive (by omega) qstar r hpos hr j (by dsimp [j]; omega)
  have hsum : qstar j*exposingWeight qstar r j ≤ scoreMoment qstar (exposingWeight qstar r) :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hn i) (exposingWeight_bounds (by omega) qstar hn r hr i).1)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le (mul_pos (hpos j) hw) hsum

/-- The real two-anchor observations force minimum-share commitments to
    be tight, then determine both the residual distribution and block. -/
theorem bounded_two_anchor_minimum_share_rigidity {m : ℕ} (hm : 2 ≤ m)
    (qstar q : Fin m → ℝ) (a : Fin 2 → ℝ)
    (htpos : ∀ j, 0 < qstar j) (htm : ∑ j, qstar j = 1/(4 : ℕ))
    (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) (hq : ∀ j, 0 ≤ q j)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1)
    (hresp : ∀ v, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights a q) v ≤ 0) : a = twoShares (((3 : ℕ) : ℝ)/(4 : ℕ)) ∧ q = qstar ∧ B = orderedBlock 1 := by
  norm_num only [Nat.cast_ofNat] at *
  classical
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let P := a 0+a 1
  let R := ∑ j, q j
  let u := P-3/4
  have ha0 : ∀ h, 0 ≤ a h := fun h => by linarith [ha h]
  have hp : 3/4 ≤ P := by dsimp [P]; linarith [ha 0,ha 1]
  have hmass : R+u = 1/4 := by
    dsimp [R,u,P]
    rw [Fin.sum_univ_two] at hnorm
    linarith
  have hsk := blockMatrix_skew (rigidityCore qstar) (rigidityCross qstar) B (twoCore_skew _) hB
  have hzero (h : Fin 2) : anchorResponse (rigidityCore qstar) (rigidityCross qstar) a q h = 0 := by
    have hz := supported_response_zero (blockWeights a q)
      (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights_nonneg a q ha0 hq) hsk hresp (.inl h) (by change 0<a h; linarith [ha h])
    simpa only [block_response_anchor] using hz
  have hf := two_anchor_variable_responses t w q a (3/4) βstar
  have hf0 := hzero 0
  have hf1 := hzero 1
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 0 = 0 at hf0
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 1 = 0 at hf1
  rw [hf.1] at hf0
  rw [hf.2] at hf1
  have hβeq : scoreMoment q w = βstar*P/(3/4) := by dsimp [P]; nlinarith
  have hβpos : 0 < βstar := exposing_moment_positive hm qstar (1/4) htpos htm
  have hβge : βstar ≤ scoreMoment q w := by rw [hβeq]; nlinarith
  have hobs := (two_anchor_observed_bounds (by omega) qstar (fun j => le_of_lt (htpos j)) htm).2
  have hscore : ∀ j, t j-u ≤ score (rigidityCross qstar) a j := by
    intro j
    have hs := congrFun (two_score t w (3/4) (by norm_num)) j
    have hd0 := (hobs j 0).1
    have hd1 := (hobs j 1).1
    have h0 : 0 ≤ (a 0-3/8)*(twoCross t w (3/4) j 0+1) :=
      mul_nonneg (by linarith [ha 0]) (by linarith)
    have h1 : 0 ≤ (a 1-3/8)*(twoCross t w (3/4) j 1+1) :=
      mul_nonneg (by linarith [ha 1]) (by linarith)
    change score (twoCross t w (3/4)) (twoShares (3/4)) j = t j at hs
    simp only [score, Fin.sum_univ_two, twoShares] at hs
    change t j-u ≤ score (twoCross t w (3/4)) a j
    simp only [score, Fin.sum_univ_two]
    dsimp [u,P]
    nlinarith
  have hres := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B a q 0).mp hresp).2
  have hc0 := completion_cuts_necessary q (score (rigidityCross qstar) a) B 1 R 0 hq rfl hB
    (fun i j => (hb i j).1) hres
  have hc : Cuts 1 (1/4) q t := by
    intro s
    have hh := hc0 s
    simp only [sub_zero, one_mul] at hh
    have hsum : (∑ j ∈ s, q j*t j) ≤ (∑ j ∈ s, q j*score (rigidityCross qstar) a j)+u*mass s q := by
      have hpoint := Finset.sum_le_sum (s := s) (f := fun j => q j*t j)
        (g := fun j => q j*(score (rigidityCross qstar) a j+u)) fun j _ =>
          mul_le_mul_of_nonneg_left (by linarith [hscore j]) (hq j)
      simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mass, mul_comm u] using hpoint
    calc
      _ ≤ mass s q*(R-mass s q)+u*mass s q := le_trans hsum (add_le_add hh le_rfl)
      _ = _ := by rw [← hmass]; ring
  have hβle := cuts_exposing_moment_le (by omega) q qstar (1/4) htm hc
  have hβ : scoreMoment q w = βstar := le_antisymm hβle hβge
  have hP : P=3/4 := by rw [hβ] at hβeq; nlinarith
  have haeq : a = twoShares (3/4) := by
    funext h
    fin_cases h
    · change a 0 = (3/4)/(2 : ℕ)
      norm_num
      dsimp [P] at hP
      linarith [ha 0,ha 1]
    · change a 1 = (3/4)/(2 : ℕ)
      norm_num
      dsimp [P] at hP
      linarith [ha 0,ha 1]
  refine ⟨haeq, ?_⟩
  have hqm : ∑ j, q j = 1/4 := by dsimp [u] at hmass; rw [hP] at hmass; dsimp [R] at hmass; linarith
  subst a
  exact two_anchor_fixed_share_uniqueness (by omega) qstar q (3/4) (1/4) (by norm_num)
    htpos hq hqm htm B hB (fun i j => (hb i j).1) hresp

end
end SparseCompletion
