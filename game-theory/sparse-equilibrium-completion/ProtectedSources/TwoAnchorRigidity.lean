/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.PrefixRigidity
public import ProtectedSources.GameModel

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def twoCore (a : ℝ) (i j : Fin 2) : ℝ :=
  if i=j then 0 else if i.val=0 then a else -a

def twoCross {m : ℕ} (t w : Fin m → ℝ) (p : ℝ) (j : Fin m) (h : Fin 2) : ℝ :=
  if h.val=0 then t j/p+w j else t j/p-w j

def twoShares (p : ℝ) : Fin 2 → ℝ := fun _ => p/(2 : ℕ)

theorem twoCore_skew (a : ℝ) : IsSkew (twoCore a) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [twoCore]

theorem two_score {m : ℕ} (t w : Fin m → ℝ) (p : ℝ) (hp : p ≠ 0) :
    score (twoCross t w p) (twoShares p) = t := by
  funext j
  simp only [score, Fin.sum_univ_two, twoCross, twoShares]
  norm_num
  field_simp
  ring

theorem two_anchor_responses {m : ℕ} (t w q : Fin m → ℝ) (p βstar : ℝ) (hp : p ≠ 0) :
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 0 =
      -scoreMoment q t/p-(scoreMoment q w-βstar) ∧
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 1 =
      -scoreMoment q t/p+(scoreMoment q w-βstar) := by
  have hsum : (∑ i, t i/p*q i) = scoreMoment q t/p := by
    unfold scoreMoment
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : (∑ i, w i*q i) = scoreMoment q w := by
    unfold scoreMoment
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor <;>
    simp only [anchorResponse, Fin.sum_univ_two, twoCore, twoCross, twoShares] <;>
    norm_num <;>
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hw] <;>
    field_simp <;> ring

/-- Fixed-share equilibrium in the two-anchor encoding forces every
    residual probability, for any prescribed target distribution. -/
theorem two_anchor_strategy_rigidity {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (p r : ℝ) (hp : 0 < p)
    (hq : ∀ j, 0 ≤ q j) (hqm : ∑ j, q j = r) (htm : ∑ j, qstar j = r)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (hresp : ∀ a, response
      (blockMatrix (twoCore (2*scoreMoment qstar (exposingWeight qstar r)/p))
        (twoCross (targetScore qstar r) (exposingWeight qstar r) p) B)
      (blockWeights (twoShares p) q) a ≤ 0) : q = qstar := by
  let t := targetScore qstar r
  let w := exposingWeight qstar r
  let βstar := scoreMoment qstar w
  let K := twoCore (2*βstar/p)
  let D := twoCross t w p
  have hs : score D (twoShares p) = t := two_score t w p (ne_of_gt hp)
  have hmean : scoreMoment q t = 0 := by
    have hh := exact_score_mean_zero K D B (twoShares p) q
      (fun _ => div_nonneg (le_of_lt hp) (by norm_num)) hq (twoCore_skew _) hB hresp
    rw [hs] at hh
    exact hh
  have ha := ((block_response_bounds_iff K D B (twoShares p) q 0).mp hresp).1
  have hf := two_anchor_responses t w q p βstar (ne_of_gt hp)
  have h0 : anchorResponse K D (twoShares p) q 0 ≤ 0 := ha 0
  have h1 : anchorResponse K D (twoShares p) q 1 ≤ 0 := ha 1
  change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 0 ≤ 0 at h0
  change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 1 ≤ 0 at h1
  rw [hf.1, hmean] at h0
  rw [hf.2, hmean] at h1
  have hβ : βstar ≤ scoreMoment q w := by simp only [neg_zero, zero_div, zero_sub] at h0; linarith
  have hrows := ((block_response_bounds_iff K D B (twoShares p) q 0).mp hresp).2
  rw [hs] at hrows
  have hc0 := completion_cuts_necessary q t B 1 r 0 hq hqm hB hb hrows
  have hc : Cuts 1 r q t := by simpa only [sub_zero] using hc0
  exact strict_prefix_rigidity hm q qstar r hqm htm hc hβ

theorem target_score_moment_zero {m : ℕ} (q : Fin m → ℝ) (r : ℝ)
    (hr : ∑ j, q j = r) : scoreMoment q (targetScore q r) = 0 := by
  have hh := skew_weighted_sum Finset.univ q (orderedBlock 1) (orderedBlock_skew 1)
  have hz : (∑ j, q j*response (orderedBlock 1) q j) = -scoreMoment q (targetScore q r) := by
    simp_rw [orderedBlock_response q r hr]
    simp only [mul_neg, Finset.sum_neg_distrib, scoreMoment]
  simp only [response, Finset.mul_sum] at hz
  simp only [mul_assoc] at hh
  rw [hh] at hz
  linarith

theorem two_anchor_target_feasible {m : ℕ} (qstar : Fin m → ℝ) (p r : ℝ) (hp : p ≠ 0)
    (htm : ∑ j, qstar j = r) :
    ∀ a, response
      (blockMatrix (twoCore (2*scoreMoment qstar (exposingWeight qstar r)/p))
        (twoCross (targetScore qstar r) (exposingWeight qstar r) p) (orderedBlock 1))
      (blockWeights (twoShares p) qstar) a = 0 := by
  let t := targetScore qstar r
  let w := exposingWeight qstar r
  let βstar := scoreMoment qstar w
  have ht : scoreMoment qstar t = 0 := target_score_moment_zero qstar r htm
  have hs : score (twoCross t w p) (twoShares p) = t := two_score t w p hp
  have hf := two_anchor_responses t w qstar p βstar hp
  intro a
  cases a with
  | inl h =>
    rw [block_response_anchor]
    fin_cases h
    · change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) qstar 0 = 0
      rw [hf.1, ht]
      simp only [βstar, neg_zero, zero_div, sub_self]
    · change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) qstar 1 = 0
      rw [hf.2, ht]
      simp only [βstar, neg_zero, zero_div, sub_self, add_zero]
  | inr j =>
    rw [block_response_residual, hs, orderedBlock_response qstar r htm]
    exact add_neg_cancel _

/-- The fixed-share encoding determines both the target mixture and the
    entire otherwise unknown residual block. -/
theorem two_anchor_fixed_share_uniqueness {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (p r : ℝ) (hp : 0 < p)
    (htpos : ∀ j, 0 < qstar j) (hq : ∀ j, 0 ≤ q j)
    (hqm : ∑ j, q j = r) (htm : ∑ j, qstar j = r)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (hresp : ∀ a, response
      (blockMatrix (twoCore ((2 : ℕ)*scoreMoment qstar (exposingWeight qstar r)/p))
        (twoCross (targetScore qstar r) (exposingWeight qstar r) p) B)
      (blockWeights (twoShares p) q) a ≤ 0) : q = qstar ∧ B = orderedBlock 1 := by
  norm_num only [Nat.cast_ofNat] at *
  have hqeq := two_anchor_strategy_rigidity hm qstar q p r hp hq hqm htm B hB hb hresp
  refine ⟨hqeq, ?_⟩
  subst q
  have hs := two_score (targetScore qstar r) (exposingWeight qstar r) p (ne_of_gt hp)
  have hzero := exact_supported_residual_zero
    (twoCore (2*scoreMoment qstar (exposingWeight qstar r)/p))
    (twoCross (targetScore qstar r) (exposingWeight qstar r) p) B (twoShares p) qstar
    (fun _ => div_nonneg (le_of_lt hp) (by norm_num)) hq (twoCore_skew _) hB hresp
  rw [hs] at hzero
  exact tight_prefix_completion_unique qstar r htpos htm B hB hb
    (fun j => hzero j (ne_of_gt (htpos j)))

theorem exposing_moment_bounds {m : ℕ} (hm : 0 < m) (qstar : Fin m → ℝ)
    (r : ℝ) (hq : ∀ j, 0 ≤ qstar j) (hr : ∑ j, qstar j = r) :
    0 ≤ scoreMoment qstar (exposingWeight qstar r) ∧
      scoreMoment qstar (exposingWeight qstar r) ≤ 2*r^2 := by
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (exposingWeight_bounds hm qstar hq r hr j).1
  · calc
      _ ≤ ∑ j, qstar j*(2*r) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (exposingWeight_bounds hm qstar hq r hr j).2 (hq j)
      _ = _ := by rw [← Finset.sum_mul, hr]; ring

/-- The arbitrary-target two-anchor observations are uniformly bounded;
    the construction does not encode probabilities using large payoffs. -/
theorem two_anchor_observed_bounds {m : ℕ} (hm : 0 < m) (qstar : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ qstar j) (hr : ∑ j, qstar j = 1/4) :
    (∀ i j, -1 ≤ twoCore (2*scoreMoment qstar (exposingWeight qstar (1/4))/(3/4)) i j ∧
      twoCore (2*scoreMoment qstar (exposingWeight qstar (1/4))/(3/4)) i j ≤ 1) ∧
    (∀ j h, -1 ≤ twoCross (targetScore qstar (1/4)) (exposingWeight qstar (1/4)) (3/4) j h ∧
      twoCross (targetScore qstar (1/4)) (exposingWeight qstar (1/4)) (3/4) j h ≤ 1) := by
  have hβ := exposing_moment_bounds hm qstar (1/4) hq hr
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp only [twoCore] <;> norm_num <;>
      constructor <;> nlinarith [hβ.1, hβ.2]
  · intro j h
    have ht := targetScore_bounds qstar hq (1/4) hr j
    have hw := exposingWeight_bounds hm qstar hq (1/4) hr j
    fin_cases h <;> simp only [twoCross] <;> norm_num <;>
      constructor <;> nlinarith [ht.1, ht.2, hw.1, hw.2]

def rigidityCore {m : ℕ} (qstar : Fin m → ℝ) : Fin 2 → Fin 2 → ℝ :=
  twoCore ((2 : ℕ)*scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ)))/((3 : ℕ)/(4 : ℕ)))

def rigidityCross {m : ℕ} (qstar : Fin m → ℝ) : Fin m → Fin 2 → ℝ :=
  twoCross (targetScore qstar (1/(4 : ℕ))) (exposingWeight qstar (1/(4 : ℕ))) ((3 : ℕ)/(4 : ℕ))

/-- A normalized bounded two-anchor game realizes any positive residual
    target as its unique fixed-share equilibrium-compatible witness. -/
theorem bounded_two_anchor_fixed_share_rigidity {m : ℕ} (hm : 0 < m)
    (qstar : Fin m → ℝ) (hpos : ∀ j, 0 < qstar j) (hmass : ∑ j, qstar j = 1/(4 : ℕ)) :
    let p := twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))
    let K := rigidityCore qstar
    let D := rigidityCross qstar
    (∀ a, 0 ≤ blockWeights p qstar a) ∧
    (∑ a, blockWeights p qstar a) = 1 ∧
    (∀ h : Fin 2, p h = ((3 : ℕ) : ℝ)/(8 : ℕ)) ∧
    IsSkew (blockMatrix K D (orderedBlock 1)) ∧
    (∀ a b, -1 ≤ blockMatrix K D (orderedBlock 1) a b ∧
      blockMatrix K D (orderedBlock 1) a b ≤ 1) ∧
    (∀ a, response (blockMatrix K D (orderedBlock 1)) (blockWeights p qstar) a = 0) ∧
    (∀ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ j, 0 ≤ q j) → (∑ j, q j = 1/(4 : ℕ)) → IsSkew B →
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) →
      (∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) →
      q = qstar ∧ B = orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  have hnonneg : ∀ j, 0 ≤ qstar j := fun j => le_of_lt (hpos j)
  have hobs := two_anchor_observed_bounds hm qstar hnonneg hmass
  refine ⟨blockWeights_nonneg _ _ (fun _ => by norm_num [twoShares]) hnonneg,
    ?_, ?_, blockMatrix_skew _ _ _ (twoCore_skew _) (orderedBlock_skew 1),
    blockMatrix_bounds _ _ _ 1 hobs.1 hobs.2 (orderedBlock_bounds 1 (by norm_num)),
    two_anchor_target_feasible qstar (3/4) (1/4) (by norm_num) hmass, ?_⟩
  · rw [blockWeights_mass, hmass]
    norm_num [Fin.sum_univ_two, twoShares]
  · intro h
    norm_num [twoShares]
  · intro q B hq hqm hB hb hresp
    exact two_anchor_fixed_share_uniqueness hm qstar q (3/4) (1/4) (by norm_num)
      hpos hq hqm hmass B hB (fun i j => (hb i j).1) hresp

def uniformTarget (m : ℕ) (r : ℝ) : Fin m → ℝ := fun _ => r/(m : ℝ)

theorem uniformTarget_mass (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (∑ j, uniformTarget m r j) = r := by
  simp only [uniformTarget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem uniformTarget_positive (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ j, 0 < uniformTarget m r j := by
  intro j
  exact div_pos hr (Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt))

theorem uniform_target_score (m : ℕ) (r : ℝ) (j : Fin m) :
    targetScore (uniformTarget m r) r j = r*(1-((2 : ℕ)*(j.val : ℝ)+1)/(m : ℝ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have heq : prefixSet j.val = Finset.Iio j := by
    ext i
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  unfold targetScore prefixMass mass
  rw [heq]
  simp only [uniformTarget, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
  ring

theorem uniform_prefix_mass (m : ℕ) (r : ℝ) (j : Fin m) :
    prefixMass (uniformTarget m r) j.val = (j.val : ℝ)*(r/(m : ℝ)) := by
  have heq : prefixSet j.val = Finset.Iio j := by
    ext i
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  unfold prefixMass mass
  rw [heq]
  simp only [uniformTarget, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]

theorem sum_tail_odds (m j : ℕ) :
    (∑ l ∈ Finset.range m, if j<l then (2*(l : ℝ)-2*(j : ℝ)-1) else 0) =
      ((m-j-1 : ℕ) : ℝ)^2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : j<m
    · rw [ite_eq_left h]
      have hsub : ((m-j-1 : ℕ) : ℝ) = (m : ℝ)-(j : ℝ)-1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      have hsub' : ((m+1-j-1 : ℕ) : ℝ) = (m : ℝ)-(j : ℝ) := by
        have hn : m+1-j-1 = m-j := by omega
        rw [hn, Nat.cast_sub (by omega)]
      change ((m-j-1 : ℕ) : ℝ)^2+(2*(m : ℝ)-2*(j : ℝ)-1) = ((m+1-j-1 : ℕ) : ℝ)^2
      rw [hsub, hsub']
      ring
    · rw [ite_eq_right h]
      have h0 : m-j-1=0 := by omega
      have h1 : m+1-j-1=0 := by omega
      simp [h0, h1]

/-- The gradient-defined weights specialize to the paper's explicit
    uniform quadratic weights, with zero-based residual labels. -/
theorem uniform_exposing_weight (m : ℕ) (r : ℝ) (j : Fin m) :
    exposingWeight (uniformTarget m r) r j = r*(((m : ℝ)-1-j.val)/(m : ℝ))^2 := by
  classical
  have hterm : ∀ l : Fin m,
      (if j ∈ prefixSet l.val then (2 : ℕ)*prefixMass (uniformTarget m r) l.val-r+
        targetScore (uniformTarget m r) r j else 0) =
      (r/(m : ℝ))*(if j.val<l.val then 2*(l.val : ℝ)-2*(j.val : ℝ)-1 else 0) := by
    intro l
    by_cases h : j.val<l.val
    · have hj : j ∈ prefixSet l.val := Finset.mem_filter.mpr ⟨Finset.mem_univ j,h⟩
      rw [ite_eq_left hj, ite_eq_left h, uniform_prefix_mass, uniform_target_score]
      norm_num only [Nat.cast_ofNat]
      ring
    · have hj : j ∉ prefixSet l.val := by simpa only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] using h
      rw [ite_eq_right hj, ite_eq_right h, mul_zero]
  unfold exposingWeight
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => if j.val<l then 2*(l : ℝ)-2*(j.val : ℝ)-1 else 0), sum_tail_odds]
  have hsub : ((m-j.val-1 : ℕ) : ℝ) = (m : ℝ)-1-j.val := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hsub]
  ring

/-- The paper's uniform construction is a specialization of the arbitrary
    positive target realization. Every residual coordinate is positive. -/
theorem uniform_two_anchor_dense (m : ℕ) (hm : 0 < m) :
    (∀ j, 0 < uniformTarget m (1/(4 : ℕ)) j) ∧
    (∑ j, uniformTarget m (1/(4 : ℕ)) j) = 1/(4 : ℕ) ∧
    (∀ a, response
      (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) (orderedBlock 1))
      (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) (uniformTarget m (1/(4 : ℕ)))) a = 0) ∧
    (∀ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ j, 0 ≤ q j) → (∑ j, q j = 1/(4 : ℕ)) → IsSkew B →
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) →
      (∀ a, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) a ≤ 0) →
      q = uniformTarget m (1/(4 : ℕ)) ∧ B = orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  have hp := uniformTarget_positive m (1/4) (by norm_num)
  have hmass := uniformTarget_mass m hm (1/4)
  refine ⟨hp, hmass, two_anchor_target_feasible _ (3/4) (1/4) (by norm_num) hmass, ?_⟩
  intro q B hq hqm hB hb hresp
  exact two_anchor_fixed_share_uniqueness hm _ q (3/4) (1/4) (by norm_num) hp hq hqm hmass
    B hB (fun i j => (hb i j).1) hresp

theorem positive_target_full_support {m : ℕ} (qstar : Fin m → ℝ)
    (hpos : ∀ j, 0 < qstar j) :
    (Finset.univ.filter fun j => qstar j ≠ 0).card = m := by
  have heq : (Finset.univ.filter fun j => qstar j ≠ 0) = Finset.univ := by
    ext j
    simp [ne_of_gt (hpos j)]
  rw [heq]
  simp

end
end SparseCompletion

