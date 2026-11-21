module

public import CoreWitness
public import EventualPlan
public import DensityReduction
public import Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition

open Filter Finset OpenProblems Sampling

/-- Theorem 1. At every positive logarithmic scale, an induced graph in the
prescribed size interval has a degree class containing the required proportion. -/
theorem logScale_repetition : LogScaleRepetition := by
  classical
  intro K hK η hη hη1
  obtain ⟨u,τ,c,C,up,tp,cp,_,density⟩ := density_reduction K hK
  let u' := min u (c/2)
  let θ := min (τ/4) (1/4)
  have up' : 0 < u' := lt_min up (by positivity)
  have hp : 0 < θ := lt_min (by positivity) (by norm_num)
  have hp' : θ < 1/2 := (min_le_right ..).trans_lt (by norm_num : (1:ℝ)/4<1/2)
  obtain ⟨L₀,L₁,a,n₁,Lp,Ls,ap,adjust⟩ := simultaneous_adjustment u' τ (c/2) θ up' tp (by positivity) hp hp'
  obtain ⟨g,hg⟩ := exists_nat_gt (8/a)
  have room : 8 ≤ a*(g:ℝ) := by have := (div_lt_iff₀ ap).mp hg; linarith
  have gp : 0 < g := by exact_mod_cast (show 0 < (g:ℝ) from (by positivity : (0:ℝ)<8/a).trans hg)
  let δ : ℝ := 1/(8*(g:ℝ))
  have dp : 0 < δ := by dsimp [δ]; positivity
  have gd : (g:ℝ)*δ ≤ 1/8 := by
    dsimp [δ]
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨ε,εp,plan⟩ := eventual_plan u' c θ η a g L₀ L₁ n₁ up' cp hp hη hη1 gp Lp Ls room
  let order := fun N : ℕ => ⌈K*Real.log N⌉₊
  have ord : Tendsto order atTop atTop := tendsto_nat_ceil_atTop.comp
    ((tendsto_const_mul_atTop_of_pos hK).mpr (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  apply eventually_atTop.mp
  filter_upwards [density ε εp,ord.eventually plan,ord.eventually (adjust 2 δ dp)] with N red plans edits
  intro G
  rcases red G with ⟨S,d,lo,hi,reg⟩ | ⟨B,p,low,_,p₀,p₁,cuts,_,op⟩
  · exact ⟨S,d,lo,hi,by rw [reg]; nlinarith [mul_nonneg hη.le (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)]⟩
  obtain ⟨design⟩ := plans B.card low
  have core := inherited_core G B (order N) u τ c low cuts
  have θτ := min_le_left (τ/4) (1/4:ℝ)
  apply core_witness G B design hp hη.le (by dsimp [θ]; linarith) (by dsimp [θ]; linarith)
    Ls op δ dp.le gd
  intro Y n ℓ ncap fresh Xs ex data short long
  exact edits N G B Y n ℓ core ncap fresh Xs ex data short long

/-- Corollary 2. The logarithm of the least repetition threshold is little-o of k. -/
theorem subexponential_threshold : SubexponentialThreshold :=
  subexponential_of_logScale logScale_repetition


/-- Section 7. After deleting the exceptional vertices, each remaining degree
decreases by the number of neighbors of that vertex in the exceptional set. -/
theorem degreeOn_delete_exceptional {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S X : Finset V) (hX : X ⊆ S) (x : V) :
    degreeOn G (S \ X) x = degreeOn G S x - degreeOn G X x := by
  classical
  unfold degreeOn
  have hf : (S \ X).filter (G.Adj x) = S.filter (G.Adj x) \ X.filter (G.Adj x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hf, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hX)]

end InducedDegreeRepetition
