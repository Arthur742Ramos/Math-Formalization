/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.SupportMinimum

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem block_entry_perturbation {α ι : Type*}
    (K K' : α → α → ℝ) (D D' : ι → α → ℝ) (B : ι → ι → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hK : ∀ i j, |K i j-K' i j| ≤ δ)
    (hD : ∀ j i, |D j i-D' j i| ≤ δ) :
    ∀ i j, |blockMatrix K D B i j-blockMatrix K' D' B i j| ≤ δ := by
  intro i j
  cases i <;> cases j
  · exact hK _ _
  · simpa only [blockMatrix, neg_sub_neg, abs_sub_comm] using hD _ _
  · exact hD _ _
  · simpa only [blockMatrix, sub_self, abs_zero] using hδ

/-- Closed clipped observation interval about a central bounded payoff. -/
def ClippedObservation (a δ x : ℝ) : Prop := -1 ≤ x ∧ x ≤ 1 ∧ |x-a| ≤ δ

theorem clipped_observation_interval (a δ x : ℝ) :
    ClippedObservation a δ x ↔ x ∈ Set.Icc (max (-1) (a-δ)) (min 1 (a+δ)) := by
  simp only [ClippedObservation, Set.mem_Icc, max_le_iff, le_min_iff, abs_le]
  constructor
  · rintro ⟨h1,h2,hlo,hup⟩
    exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
  · rintro ⟨⟨h1,hlo⟩,h2,hup⟩
    exact ⟨h1,h2,by constructor <;> linarith⟩

/-- The residual block is free; precisely the anchor-incident entries are
    restricted to their clipped uncertainty intervals. -/
def UniformIntervalWitness (m : ℕ) (ε δ : ℝ) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ)
    (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) ∧
    (fixed=true → a=twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) ∧
    (∑ h, a h)+(∑ j, q j)=1 ∧ IsSkew K ∧ IsSkew B ∧
    (∀ i j, ClippedObservation (rigidityCore (uniformTarget m (1/(4 : ℕ))) i j) δ (K i j)) ∧
    (∀ j h, ClippedObservation (rigidityCross (uniformTarget m (1/(4 : ℕ))) j h) δ (D j h)) ∧
    (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
    ∀ v, response (blockMatrix K D B) (blockWeights a q) v ≤ ε

theorem uniform_interval_restore {m : ℕ} {ε δ : ℝ} {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {K : Fin 2 → Fin 2 → ℝ} {D : Fin m → Fin 2 → ℝ} {B : Fin m → Fin m → ℝ}
    (hδ : 0 ≤ δ) (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    UniformWitness m (ε+δ) fixed a q B := by
  rcases hw with ⟨hq,ha,hfixed,hmass,_,hB,hK,hD,hb,hresp⟩
  unfold UniformWitness
  norm_num only [Nat.cast_ofNat]
  refine ⟨hq,ha,hfixed,hmass,hB,hb,?_⟩
  intro v
  have hp : ∀ h, 0 ≤ a h := fun h => by linarith [ha h]
  have hh := response_perturbation
    (blockMatrix (rigidityCore (uniformTarget m (1/4))) (rigidityCross (uniformTarget m (1/4))) B)
    (blockMatrix K D B) (blockWeights a q) δ 1
    (blockWeights_nonneg a q hp hq)
    (by rw [blockWeights_mass]; exact hmass)
    (block_entry_perturbation _ _ _ _ _ δ hδ
      (fun i j => by simpa only [abs_sub_comm,Nat.cast_ofNat] using (hK i j).2.2)
      (fun j h => by simpa only [abs_sub_comm,Nat.cast_ofNat] using (hD j h).2.2)) v
  have hup := (abs_le.mp hh).2
  linarith [hresp v]


theorem uniform_interval_total_support_card {m : ℕ} {ε δ : ℝ} {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {K : Fin 2 → Fin 2 → ℝ} {D : Fin m → Fin 2 → ℝ} {B : Fin m → Fin m → ℝ}
    (hδ : 0 ≤ δ) (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    (Finset.univ.filter fun v => blockWeights a q v ≠ 0).card = supportSize q+2 := by
  exact uniform_witness_total_support_card (uniform_interval_restore hδ hw)

theorem uniform_interval_total_support_lower {m : ℕ} (hm : 0 < m)
    {ε δ : ℝ} (heff : 0 < ε+δ) (hδ : 0 ≤ δ) {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {K : Fin 2 → Fin 2 → ℝ} {D : Fin m → Fin 2 → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+δ)) ≤ (supportSize q : ℝ)+2 := by
  norm_num only [Nat.cast_ofNat] at *
  have hr := uniform_interval_restore hδ hw
  simp only [UniformWitness,Nat.cast_ofNat] at hr
  rcases hr with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  exact uniform_total_support_lower hm q a hq ha hnorm B hB (fun i j => (hb i j).1)
    (ε+δ) heff hresp


theorem uniform_interval_dense (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) :
    UniformIntervalWitness m ε δ fixed (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) (uniformTarget m (1/(4 : ℕ)))
      (rigidityCore (uniformTarget m (1/(4 : ℕ)))) (rigidityCross (uniformTarget m (1/(4 : ℕ))))
      (orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  have hdense := uniform_witness_dense m hm ε hε fixed
  simp only [UniformWitness,Nat.cast_ofNat] at hdense
  rcases hdense with ⟨hq,ha,hfixed,hmass,hB,hb,hresp⟩
  have hobs := two_anchor_observed_bounds hm (uniformTarget m (1/4)) hq
    (uniformTarget_mass m hm (1/4))
  change (∀ i j, -1 ≤ rigidityCore (uniformTarget m (1/4)) i j ∧
      rigidityCore (uniformTarget m (1/4)) i j ≤ 1) ∧
    (∀ j h, -1 ≤ rigidityCross (uniformTarget m (1/4)) j h ∧
      rigidityCross (uniformTarget m (1/4)) j h ≤ 1) at hobs
  refine ⟨hq,ha,(by simp),hmass,twoCore_skew _,hB,?_,?_,hb,hresp⟩
  · intro i j
    exact ⟨(hobs.1 i j).1,(hobs.1 i j).2,by simpa using hδ⟩
  · intro j h
    exact ⟨(hobs.2 j h).1,(hobs.2 j h).2,by simpa using hδ⟩

theorem uniform_interval_support_exists (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) :
    ∃ s : ℕ, ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ)
      (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ) (B : Fin m → Fin m → ℝ),
      UniformIntervalWitness m ε δ fixed a q K D B ∧ supportSize q+2=s := by
  exact ⟨supportSize (uniformTarget m (1/4))+2,twoShares (3/4),uniformTarget m (1/4),
    rigidityCore _,rigidityCross _,orderedBlock 1,uniform_interval_dense m hm ε δ hε hδ fixed,rfl⟩

def uniformMinimumIntervalTotalSupport (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) : ℕ := by
  classical
  exact Nat.find (uniform_interval_support_exists m hm ε δ hε hδ fixed)

theorem uniformMinimumIntervalTotalSupport_attained (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) :
    ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ)
      (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ) (B : Fin m → Fin m → ℝ),
      UniformIntervalWitness m ε δ fixed a q K D B ∧
        supportSize q+2=uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed := by
  classical
  exact Nat.find_spec (uniform_interval_support_exists m hm ε δ hε hδ fixed)

theorem uniformMinimumIntervalTotalSupport_lower (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (heff : 0 < ε+δ) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+δ)) ≤
      (uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed : ℝ) := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨a,q,K,D,B,hw,hcount⟩ :=
    uniformMinimumIntervalTotalSupport_attained m hm ε δ hε hδ fixed
  have hlower := uniform_interval_total_support_lower hm heff hδ hw
  have heq : (supportSize q : ℝ)+2 =
      (uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed : ℝ) := by exact_mod_cast hcount
  rwa [heq] at hlower


theorem uniform_exact_to_interval {m : ℕ} (hm : 0 < m) {ε δ : ℝ} (hδ : 0 ≤ δ)
    {fixed : Bool} {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε fixed a q B) :
    UniformIntervalWitness m ε δ fixed a q (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B := by
  norm_num only [Nat.cast_ofNat] at *
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨hq,ha,hfixed,hmass,hB,hb,hresp⟩
  have hobs := two_anchor_observed_bounds hm (uniformTarget m (1/4))
    (fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j))
    (uniformTarget_mass m hm (1/4))
  change (∀ i j, -1 ≤ rigidityCore (uniformTarget m (1/4)) i j ∧
      rigidityCore (uniformTarget m (1/4)) i j ≤ 1) ∧
    (∀ j h, -1 ≤ rigidityCross (uniformTarget m (1/4)) j h ∧
      rigidityCross (uniformTarget m (1/4)) j h ≤ 1) at hobs
  refine ⟨hq,ha,hfixed,hmass,twoCore_skew _,hB,?_,?_,hb,hresp⟩
  · intro i j
    exact ⟨(hobs.1 i j).1,(hobs.1 i j).2,by simpa using hδ⟩
  · intro j h
    exact ⟨(hobs.2 j h).1,(hobs.2 j h).2,by simpa using hδ⟩

theorem uniformMinimumIntervalTotalSupport_le (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ) (B : Fin m → Fin m → ℝ)
    (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed ≤ supportSize q+2 := by
  classical
  exact Nat.find_min' (uniform_interval_support_exists m hm ε δ hε hδ fixed) ⟨a,q,K,D,B,hw,rfl⟩

theorem uniformMinimumIntervalTotalSupport_radius_zero (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 ≤ ε) (fixed : Bool) :
    uniformMinimumIntervalTotalSupport m hm ε 0 hε (le_refl 0) fixed =
      uniformMinimumTotalSupport m hm ε hε fixed := by
  apply Nat.le_antisymm
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m hm ε hε fixed
    have hle := uniformMinimumIntervalTotalSupport_le m hm ε 0 hε (by norm_num) fixed
      a q _ _ B (uniform_exact_to_interval hm (by norm_num) hw)
    rwa [hcount] at hle
  · obtain ⟨a,q,K,D,B,hw,hcount⟩ :=
      uniformMinimumIntervalTotalSupport_attained m hm ε 0 hε (by norm_num) fixed
    have hcentral : UniformWitness m ε fixed a q B := by
      simpa only [add_zero] using uniform_interval_restore (by norm_num : (0 : ℝ) ≤ 0) hw
    have hle := uniformMinimumTotalSupport_le m hm ε hε fixed a q B hcentral
    rwa [hcount] at hle

theorem uniformMinimumIntervalTotalSupport_origin (m : ℕ) (hm : 2 ≤ m) (fixed : Bool) :
    uniformMinimumIntervalTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 0 (le_refl 0) (le_refl 0) fixed = m+2 := by
  rw [uniformMinimumIntervalTotalSupport_radius_zero]
  exact uniformMinimumTotalSupport_zero m hm fixed

end
end SparseCompletion
