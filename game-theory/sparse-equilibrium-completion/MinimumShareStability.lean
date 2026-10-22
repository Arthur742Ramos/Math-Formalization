/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import PrefixStability

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- A supported row's lower response follows from the whole normalized
    skew game and a lower probability share. -/
theorem response_lower_from_share {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) (hA : IsSkew A)
    (hx : ∀ j, 0 ≤ x j) (hmass : ∑ j, x j = 1)
    (z c : ℝ) (hresp : ∀ j, response A x j ≤ z) (i : ι) (hshare : c ≤ x i) :
    (c-1)*z ≤ c*response A x i := by
  have hcancel := skew_weighted_sum Finset.univ x A hA
  have hzero : (∑ j, x j*response A x j) = 0 := by
    simpa only [response, Finset.mul_sum, mul_assoc] using hcancel
  have hsum : (∑ j, x j*(z-response A x j)) = z := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul, hzero, sub_zero]
  have hn : ∀ j, 0 ≤ x j*(z-response A x j) := fun j =>
    mul_nonneg (hx j) (sub_nonneg.mpr (hresp j))
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hn j) (Finset.mem_univ i)
  rw [hsum] at hi
  have hc := mul_le_mul_of_nonneg_right hshare (sub_nonneg.mpr (hresp i))
  nlinarith

theorem cuts_with_score_lower_shift {ι : Type*} [Fintype ι]
    (q t v : ι → ℝ) (R r u z : ℝ) (hq : ∀ j, 0 ≤ q j) (hmass : R+u=r)
    (hscore : ∀ j, t j-u ≤ v j) (hc : Cuts 1 R q (fun j => v j-z)) :
    Cuts 1 r q (fun j => t j-z) := by
  intro s
  have hh := hc s
  simp only [one_mul] at hh
  have hsum : (∑ j ∈ s, q j*(t j-z)) ≤
      (∑ j ∈ s, q j*(v j-z))+u*mass s q := by
    have hp := Finset.sum_le_sum (s := s) (f := fun j => q j*(t j-z))
      (g := fun j => q j*((v j-z)+u)) fun j _ =>
        mul_le_mul_of_nonneg_left (by linarith [hscore j]) (hq j)
    simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mass, mul_comm u] using hp
  calc
    _ ≤ mass s q*(R-mass s q)+u*mass s q := le_trans hsum (add_le_add hh le_rfl)
    _ = _ := by rw [← hmass]; ring

/-- The same prefix error bound holds with only two minimum-share
    commitments, even when the candidate residual mass is smaller. -/
theorem two_anchor_minimum_share_stability {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (a : Fin 2 → ℝ)
    (htpos : ∀ j, 0 ≤ qstar j) (htm : ∑ j, qstar j = 1/(4 : ℕ))
    (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) (hq : ∀ j, 0 ≤ q j)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights a q) v ≤ z) : prefixError q qstar ≤ z*(1/(4 : ℕ)+1/(((3 : ℕ) : ℝ)/(4 : ℕ))) := by
  norm_num only [Nat.cast_ofNat] at *
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let P := a 0+a 1
  let R := ∑ j, q j
  let u := P-3/4
  have ha0 : ∀ h, 0 ≤ a h := fun h => by linarith [ha h]
  have hp : 3/4 ≤ P := by dsimp [P]; linarith [ha 0,ha 1]
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hmass : R+u=1/4 := by dsimp [R,u,P]; rw [Fin.sum_univ_two] at hnorm; linarith
  have hβ0 : 0 ≤ βstar := (exposing_moment_bounds hm qstar (1/4) htpos htm).1
  have hsk := blockMatrix_skew (rigidityCore qstar) (rigidityCross qstar) B (twoCore_skew _) hB
  have hallmass : (∑ v, blockWeights a q v) = 1 := by rw [blockWeights_mass]; exact hnorm
  have hlow := response_lower_from_share (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
    (blockWeights a q) hsk (blockWeights_nonneg a q ha0 hq) hallmass z (3/8) hresp (.inl 1) (ha 1)
  rw [block_response_anchor] at hlow
  have hup := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B a q z).mp hresp).1 0
  have hf := two_anchor_variable_responses t w q a (3/4) βstar
  change (3/8-1)*z ≤ (3/8)*anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 1 at hlow
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 0 ≤ z at hup
  rw [hf.2] at hlow
  rw [hf.1] at hup
  have hβprod : 0 ≤ βstar*(P-3/4) := mul_nonneg hβ0 (by linarith)
  have hβ : -(z/(3/4)) ≤ scoreMoment q w-βstar := by dsimp [P] at hβprod; nlinarith
  have hobs := (two_anchor_observed_bounds hm qstar htpos htm).2
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
  have hres := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B a q z).mp hresp).2
  have hc0 := completion_cuts_necessary q (score (rigidityCross qstar) a) B 1 R z hq rfl hB hb hres
  have hc := cuts_with_score_lower_shift q t (score (rigidityCross qstar) a) R (1/4) u z hq hmass hscore hc0
  have hR : (∑ j, q j) ≤ 1/4 := by change R ≤ 1/4; linarith
  have hh := prefix_error_from_cuts hm q qstar (1/4) z (z/(3/4)) hq hR htm hz hc hβ
  nlinarith

end
end SparseCompletion
