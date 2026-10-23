/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalLower

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem two_core_response_perturbation {ι : Type*} [Fintype ι]
    (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ) (q : ι → ℝ)
    (u v δ : ℝ) (hδ : 0 ≤ δ) (huv : |u-v| ≤ δ) :
    ∀ i, |response (blockMatrix (twoCore u) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) i-
      response (blockMatrix (twoCore v) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) i| ≤ (((3 : ℕ) : ℝ)/(8 : ℕ))*δ := by
  norm_num only [Nat.cast_ofNat] at *
  intro i
  cases i with
  | inl h =>
    rw [block_response_anchor,block_response_anchor]
    fin_cases h
    · change |anchorResponse (twoCore u) D (twoShares (3/4)) q 0-
        anchorResponse (twoCore v) D (twoShares (3/4)) q 0| ≤ (3/8)*δ
      have heq : anchorResponse (twoCore u) D (twoShares (3/4)) q 0-
          anchorResponse (twoCore v) D (twoShares (3/4)) q 0 = (u-v)*(3/8) := by
        simp [anchorResponse,Fin.sum_univ_two,twoCore,twoShares]
        ring
      rw [heq,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/8)]
      nlinarith
    · change |anchorResponse (twoCore u) D (twoShares (3/4)) q 1-
        anchorResponse (twoCore v) D (twoShares (3/4)) q 1| ≤ (3/8)*δ
      have heq : anchorResponse (twoCore u) D (twoShares (3/4)) q 1-
          anchorResponse (twoCore v) D (twoShares (3/4)) q 1 = -(u-v)*(3/8) := by
        simp [anchorResponse,Fin.sum_univ_two,twoCore,twoShares]
        ring
      rw [heq,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/8)]
      nlinarith
  | inr j =>
    rw [block_response_residual,block_response_residual,sub_self,abs_zero]
    positivity

/-- Exact cross observations, fixed anchor shares, and uncertainty solely
    in the single unordered anchor-core entry. -/
def UniformCoreWitness (m : ℕ) (ε δ : ℝ) (q : Fin m → ℝ) (u : ℝ)
    (B : Fin m → Fin m → ℝ) : Prop :=
  UniformIntervalWitness m ε δ true (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q (twoCore u)
    (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B

theorem uniform_core_restore {m : ℕ} {ε δ : ℝ} {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (hδ : 0 ≤ δ) (hw : UniformCoreWitness m ε δ q u B) :
    UniformWitness m (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) true (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q B := by
  norm_num only [Nat.cast_ofNat] at *
  rcases hw with ⟨hq,ha,_,hmass,_,hB,hK,_,hb,hresp⟩
  let c := (2 : ℕ)*scoreMoment (uniformTarget m (1/4))
    (exposingWeight (uniformTarget m (1/4)) (1/4))/((3 : ℕ)/(4 : ℕ))
  have hnear : |u-c| ≤ δ := by
    simpa [rigidityCore,twoCore,c] using (hK 0 1).2.2
  have hpert := two_core_response_perturbation (rigidityCross (uniformTarget m (1/4))) B q
    c u δ hδ (by simpa only [abs_sub_comm] using hnear)
  unfold UniformWitness
  norm_num only [Nat.cast_ofNat]
  refine ⟨hq,ha,(by simp),hmass,hB,hb,?_⟩
  intro v
  have hh := (abs_le.mp (hpert v)).2
  change response (blockMatrix (twoCore c) (rigidityCross (uniformTarget m (1/4))) B)
      (blockWeights (twoShares (3/4)) q) v ≤ ε+(3/8)*δ
  linarith [hresp v]

theorem uniform_core_total_support_lower {m : ℕ} (hm : 0 < m) {ε δ : ℝ}
    (heff : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) (hδ : 0 ≤ δ) {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (hw : UniformCoreWitness m ε δ q u B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) ≤ (supportSize q : ℝ)+2 := by
  norm_num only [Nat.cast_ofNat] at *
  have hr := uniform_core_restore hδ hw
  simp only [UniformWitness,Nat.cast_ofNat] at hr
  rcases hr with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  exact uniform_total_support_lower hm q (twoShares (3/4)) hq ha hnorm B hB
    (fun i j => (hb i j).1) (ε+(3/8)*δ) heff hresp


/-- The central bounded anchor-core payoff of the uniform family. -/
def uniformCoreValue (m : ℕ) : ℝ :=
  (2 : ℕ)*scoreMoment (uniformTarget m (1/(4 : ℕ)))
    (exposingWeight (uniformTarget m (1/(4 : ℕ))) (1/(4 : ℕ)))/((3 : ℕ)/(4 : ℕ))

theorem uniform_core_dense (m : ℕ) (hm : 0 < m) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    UniformCoreWitness m ε δ (uniformTarget m (1/(4 : ℕ))) (uniformCoreValue m) (orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  exact uniform_interval_dense m hm ε δ hε hδ true

theorem uniform_core_support_exists (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    ∃ s : ℕ, ∃ (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ),
      UniformCoreWitness m ε δ q u B ∧ supportSize q+2=s := by
  exact ⟨supportSize (uniformTarget m (1/4))+2,uniformTarget m (1/4),uniformCoreValue m,
    orderedBlock 1,uniform_core_dense m hm ε δ hε hδ,rfl⟩

def uniformMinimumCoreTotalSupport (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) : ℕ := by
  classical
  exact Nat.find (uniform_core_support_exists m hm ε δ hε hδ)

theorem uniformMinimumCoreTotalSupport_attained (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    ∃ (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ),
      UniformCoreWitness m ε δ q u B ∧
        supportSize q+2=uniformMinimumCoreTotalSupport m hm ε δ hε hδ := by
  classical
  exact Nat.find_spec (uniform_core_support_exists m hm ε δ hε hδ)

theorem uniformMinimumCoreTotalSupport_le (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ)
    (hw : UniformCoreWitness m ε δ q u B) :
    uniformMinimumCoreTotalSupport m hm ε δ hε hδ ≤ supportSize q+2 := by
  classical
  exact Nat.find_min' (uniform_core_support_exists m hm ε δ hε hδ) ⟨q,u,B,hw,rfl⟩

theorem uniform_core_total_support_card {m : ℕ} {ε δ : ℝ} {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (hδ : 0 ≤ δ) (hw : UniformCoreWitness m ε δ q u B) :
    (Finset.univ.filter fun v => blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q v ≠ 0).card = supportSize q+2 := by
  norm_num only [Nat.cast_ofNat] at *
  exact uniform_witness_total_support_card (uniform_core_restore hδ hw)

theorem uniformMinimumCoreTotalSupport_lower (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (heff : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) ≤
      (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨q,u,B,hw,hcount⟩ := uniformMinimumCoreTotalSupport_attained m hm ε δ hε hδ
  have hh := uniform_core_total_support_lower hm heff hδ hw
  have heq : (supportSize q : ℝ)+2 =
      (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) := by exact_mod_cast hcount
  rwa [heq] at hh

theorem uniformMinimumCoreTotalSupport_radius_zero (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 ≤ ε) :
    uniformMinimumCoreTotalSupport m hm ε 0 hε (le_refl 0) =
      uniformMinimumTotalSupport m hm ε hε true := by
  apply Nat.le_antisymm
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m hm ε hε true
    have ha := hw.2.2.1 rfl
    subst a
    have hinterval := uniform_exact_to_interval hm (le_refl 0) hw
    have hle := uniformMinimumCoreTotalSupport_le m hm ε 0 hε (le_refl 0) q
      (uniformCoreValue m) B hinterval
    rwa [hcount] at hle
  · obtain ⟨q,u,B,hw,hcount⟩ := uniformMinimumCoreTotalSupport_attained m hm ε 0 hε (le_refl 0)
    have hcentral : UniformWitness m ε true (twoShares (3/4)) q B := by
      simpa only [mul_zero,add_zero,Nat.cast_ofNat] using uniform_core_restore (le_refl 0) hw
    have hle := uniformMinimumTotalSupport_le m hm ε hε true (twoShares (3/4)) q B hcentral
    rwa [hcount] at hle

theorem uniformMinimumCoreTotalSupport_origin (m : ℕ) (hm : 2 ≤ m) :
    uniformMinimumCoreTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 0
      (le_refl 0) (le_refl 0) = m+2 := by
  rw [uniformMinimumCoreTotalSupport_radius_zero]
  exact uniformMinimumTotalSupport_zero m hm true

end
end SparseCompletion
