/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import MinimumShareRigidity

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def prefixError {m : ℕ} (q qstar : Fin m → ℝ) : ℝ :=
  (∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2)/(m : ℝ)

theorem shifted_cut_prefix_gap {m : ℕ} (q t : Fin m → ℝ) (r z : ℝ)
    (hc : Cuts 1 r q (fun j => t j-z)) (l : ℕ) :
    prefixGap q t r l ≤ z*prefixMass q l := by
  have hh := hc (prefixSet l)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, one_mul] at hh
  unfold mass at hh
  unfold prefixGap prefixMass mass
  nlinarith

/-- Prefix error stability needs only an upper bound on candidate total
    mass. This includes the variable-mass minimum-share setting. -/
theorem prefix_error_from_cuts {m : ℕ} (hm : 0 < m) (q qstar : Fin m → ℝ)
    (r z a : ℝ) (hq : ∀ j, 0 ≤ q j) (hqm : (∑ j, q j) ≤ r)
    (htm : ∑ j, qstar j = r) (hz : 0 ≤ z)
    (hc : Cuts 1 r q (fun j => targetScore qstar r j-z))
    (hβ : -a ≤ scoreMoment q (exposingWeight qstar r)-scoreMoment qstar (exposingWeight qstar r)) :
    prefixError q qstar ≤ z*r+a := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hid := prefix_exposing_identity q qstar r htm
  have hsum : (∑ l : Fin m, prefixGap q (targetScore qstar r) r l.val)/(m : ℝ) ≤ z*r := by
    apply (div_le_iff₀ hmR).mpr
    calc
      _ ≤ ∑ _l : Fin m, z*r := Finset.sum_le_sum fun l _ =>
        le_trans (shifted_cut_prefix_gap q (targetScore qstar r) r z hc l.val)
          (mul_le_mul_of_nonneg_left (le_trans
            (prefixMass_le_total q hq (∑ j, q j) rfl l.val) hqm) hz)
      _ = _ := by simp; ring
  change scoreMoment q (exposingWeight qstar r)-scoreMoment qstar (exposingWeight qstar r)+
    prefixError q qstar = _ at hid
  linarith

theorem cut_full_moment_bound {ι : Type*} [Fintype ι] (q t : ι → ℝ) (r z : ℝ)
    (hmass : ∑ j, q j = r) (hc : Cuts 1 r q (fun j => t j-z)) :
    (∑ j, q j*t j) ≤ z*r := by
  have hh := hc Finset.univ
  simp only [mass, hmass, sub_self, mul_zero, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul] at hh
  nlinarith

/-- The paper's fixed-share quadratic stability estimate, for every
    prescribed target distribution (not only the uniform target). -/
theorem two_anchor_fixed_share_stability {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hqm : ∑ j, q j = 1/(4 : ℕ)) (htm : ∑ j, qstar j = 1/(4 : ℕ))
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ z) :
    prefixError q qstar ≤ z*(1/(4 : ℕ)+1/(((3 : ℕ) : ℝ)/(4 : ℕ))) := by
  norm_num only [Nat.cast_ofNat] at *
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  have hs : score (rigidityCross qstar) (twoShares (3/4)) = t := two_score t w (3/4) (by norm_num)
  have hres := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B
    (twoShares (3/4)) q z).mp hresp).2
  rw [hs] at hres
  have hc := completion_cuts_necessary q t B 1 (1/4) z hq hqm hB hb hres
  have hα : scoreMoment q t ≤ z*(1/4) := cut_full_moment_bound q t (1/4) z hqm hc
  have hanchor := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B
    (twoShares (3/4)) q z).mp hresp).1 0
  have hf := (two_anchor_responses t w q (3/4) βstar (by norm_num)).1
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 0 ≤ z at hanchor
  rw [hf] at hanchor
  have hβ : -(z/(3/4)) ≤ scoreMoment q w-βstar := by nlinarith
  have hh := prefix_error_from_cuts hm q qstar (1/4) z (z/(3/4)) hq (le_of_eq hqm) htm hz hc hβ
  nlinarith

end
end SparseCompletion
