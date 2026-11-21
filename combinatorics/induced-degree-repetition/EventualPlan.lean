module

public import PlanErrors
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Filter
open scoped Topology Classical

theorem linear_growth (u : ℝ) (hu : 0 < u) (C : ℝ) : ∀ᶠ r : ℕ in atTop, C ≤ u*r := by
  obtain ⟨n,hn⟩ := exists_nat_gt (C/u)
  filter_upwards [eventually_ge_atTop n] with r hr
  have h := (div_lt_iff₀ hu).mp (hn.trans_le (by exact_mod_cast hr : (n:ℝ)≤r))
  linarith

set_option maxHeartbeats 800000 in
theorem eventual_plan (u c θ η a : ℝ) (g L₀ L₁ n₁ : ℕ) (up : 0 < u) (cp : 0 < c)
    (hp : 0 < θ) (ep : 0 < η) (e1 : η < 1) (gp : 0 < g) (Lpos : 0 < L₀) (Ls : L₀ < L₁)
    (room : 8 ≤ a*g) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ r : ℕ in atTop, ∀ M : ℕ, Real.exp (c*r) ≤ M →
      Nonempty (SamplingPlan r M g L₀ L₁ n₁ u θ η a ε) := by
  let α := η/(16*g)
  let δ := θ/(4*(g+2))
  let z := η*(δ*α)^2/16
  have gpos : (0:ℝ)<g := by exact_mod_cast gp
  have gone : (1:ℝ)≤g := by exact_mod_cast gp
  have ap : 0 < α := by dsimp [α]; positivity
  have dp : 0 < δ := by dsimp [δ]; positivity
  have zp : 0 < z := by dsimp [z]; positivity
  have a1 : α ≤ 1 := by dsimp [α]; rw [div_le_one (by positivity)]; linarith
  have ag : α*g = η/16 := by dsimp [α]; field_simp
  have dg : δ*(g+2) = θ/4 := by dsimp [δ]; field_simp
  obtain ⟨ε,εp,accuracy,bias⟩ := spectral_accuracy g η δ z gpos ep dp zp
  refine ⟨ε,εp,?_⟩
  filter_upwards [eventual_block_sizes g (L₀+L₁) n₁ α a gp (by omega) ap a1 room,
    polynomial_below_exp c 600 cp (by norm_num) 2,polynomial_below_exp (u/16) 4 (by positivity) (by norm_num) 1,
    linear_growth (θ*α) (by positivity) 4,linear_growth (η*δ^2*α) (by positivity) (1280*g*L₁^2),
    linear_growth (z^2) (by positivity) 12000] with r sizes growth cut rm large spectral
  intro M Mbig
  let L := L₀+L₁
  let k := ⌈α*(r:ℝ)/L⌉₊
  let s := ⌈4*(r:ℝ)/g⌉₊
  let m := k*L
  let t := g*m
  let b := M/(2*t)
  obtain ⟨rp,kp,kg,ncap,hlo,hhi,ext,fresh,ml,mh⟩ := sizes
  change g*s ≤ 5*r at hhi
  change α*r ≤ (m:ℝ) at ml
  change (m:ℝ) ≤ 2*α*r at mh
  have rpos : (0:ℝ)<r := by exact_mod_cast rp
  have mp : 0 < m := Nat.cast_pos.mp ((mul_pos ap rpos).trans_le ml)
  have mpos : (0:ℝ)<m := by exact_mod_cast mp
  have tp : 0 < t := Nat.mul_pos gp mp
  have tsmall : (t:ℝ) ≤ η*r/8 := by
    change ((g*m:ℕ):ℝ) ≤ _
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left mh gpos.le,congrArg (·*(r:ℝ)) ag]
  have tail : t<r := by exact_mod_cast tsmall.trans_lt (by nlinarith [mul_lt_mul_of_pos_right e1 rpos] : η*(r:ℝ)/8 < (r:ℝ))
  have mega := growth.trans Mbig
  have mass : 4*t ≤ M := by
    have tr : (t:ℝ) < r := by exact_mod_cast tail
    have r1 : (1:ℝ) ≤ r := by exact_mod_cast rp
    exact_mod_cast (by nlinarith [mul_le_mul_of_nonneg_right r1 rpos.le] : 4*(t:ℝ) ≤ M)
  obtain ⟨bp,space,Mb,test,half⟩ := pool_sizes M t tp mass
  change M ≤ 4*t*b at Mb
  have tP : 0 < M/2 := bp.trans_le half
  have cut' : 4*(t:ℝ) ≤ Real.exp ((u/16)*r) := (by
    simp only [pow_one] at cut
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr tail.le) (by norm_num : (0:ℝ)≤4)).trans cut)
  let v := δ*m
  let κ := z*r^2
  let count := η*r/8
  let D := 2*m*L₁^2+24*ε^2*g*(m:ℝ)^2
  have vp : 0 < v := by dsimp [v]; positivity
  have kc : 0 < κ := by dsimp [κ]; positivity
  have cnt : 0 < count := by dsimp [count]; positivity
  have enough_m : 1280*(g:ℝ)*L₁^2 ≤ η*δ^2*m := by
    nlinarith only [large,mul_le_mul_of_nonneg_left ml (mul_nonneg ep.le (sq_nonneg δ))]
  have ex : (2*r:ℕ)*κ/v^2 ≤ η*r/8 := by
    rw [div_le_iff₀ (pow_pos vp 2)]
    have sq := (sq_le_sq₀ (mul_nonneg dp.le (mul_nonneg ap.le rpos.le)) vp.le).mpr (mul_le_mul_of_nonneg_left ml dp.le)
    dsimp [κ,v,z] at *
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left sq (mul_nonneg ep.le rpos.le)]
  refine ⟨⟨k,s,m,b,v,κ,count,D,rfl,kg,ncap,fresh,ext,hlo,tail,bp,test,tP,space,
    pool_large _ _ _ _ _ Mb cut',half,vp,kc,cnt,?_,?_,?_,?_,?_,?_⟩⟩
  · dsimp [v]
    nlinarith only [rm,mul_le_mul_of_nonneg_left ml hp.le,congrArg (·*(m:ℝ)) dg]
  · change _+count+(t:ℝ) ≤ _
    dsimp [count]
    nlinarith only [ex,tsmall,mul_nonneg ep.le rpos.le]
  · rw [div_le_iff₀ (by exact_mod_cast tP : (0:ℝ)<(M/2:ℕ))]
    have h : ((g*s:ℕ):ℝ) ≤ 5*r := by exact_mod_cast hhi
    have sq := pow_le_pow_left₀ (Nat.cast_nonneg (g*s) : (0:ℝ)≤(g*s:ℕ)) h 2
    have T : (M:ℝ) ≤ 3*(M/2:ℕ) := by exact_mod_cast test
    nlinarith only [sq,mega,T]
  · exact tester_budget _ _ _ _ (Nat.cast_nonneg _) rpos.le (by exact_mod_cast hhi) accuracy spectral
  · have nle : k+k ≤ m := by dsimp [m,L]; nlinarith only [Nat.mul_le_mul_left k (show 2 ≤ L₀+L₁ by omega)]
    apply variance_budget _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast tP) (by exact_mod_cast bp) gpos.le mpos.le
      (by exact_mod_cast nle) _ (by exact_mod_cast test)
    exact_mod_cast (by simpa [t,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Mb : M ≤ 4*g*m*b)
  · exact reference_budget _ _ _ _ _ _ _ _ rpos.le gpos.le mpos dp (by exact_mod_cast hhi) bias enough_m

end InducedDegreeRepetition.Sampling
