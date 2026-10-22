/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import SupportRate

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Actual witnesses in the uniform observed game. `fixed=true` adds
    exact anchor shares; both classes retain the two minimum shares. -/
def UniformWitness (m : ℕ) (ε : ℝ) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) ∧
    (fixed=true → a=twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) ∧
    (∑ h, a h)+(∑ j, q j)=1 ∧
    IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
    ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ ε

/-- The integer count minimized below is the actual support of the full strategy. -/
theorem uniform_witness_total_support_card {m : ℕ} {ε : ℝ} {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε fixed a q B) :
    (Finset.univ.filter fun v => blockWeights a q v ≠ 0).card = supportSize q+2 := by
  apply two_anchor_total_support_card
  intro h
  have hh := hw.2.1 h
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem uniform_witness_dense (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    UniformWitness m ε fixed (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) (uniformTarget m (1/(4 : ℕ))) (orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  unfold UniformWitness
  norm_num only [Nat.cast_ofNat]
  have hmass := uniformTarget_mass m hm (1/4)
  refine ⟨fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j),
    fun _ => by norm_num [twoShares], (by simp), ?_, orderedBlock_skew 1,
    orderedBlock_bounds 1 (by norm_num), ?_⟩
  · rw [hmass, Fin.sum_univ_two]
    norm_num [twoShares]
  · intro v
    exact le_trans (le_of_eq (two_anchor_target_feasible _ (3/4) (1/4) (by norm_num) hmass v)) hε

theorem uniform_witness_support_exists (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ s : ℕ, ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      UniformWitness m ε fixed a q B ∧ supportSize q+2=s := by
  exact ⟨supportSize (uniformTarget m (1/4))+2, twoShares (3/4),uniformTarget m (1/4),
    orderedBlock 1, uniform_witness_dense m hm ε hε fixed,rfl⟩

/-- A genuine attained integer minimum over actual completions and
    strategies. Nonemptiness is supplied by the dense exact witness. -/
def uniformMinimumTotalSupport (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : ℕ :=
  by
    classical
    exact Nat.find (uniform_witness_support_exists m hm ε hε fixed)

theorem uniformMinimumTotalSupport_attained (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      UniformWitness m ε fixed a q B ∧
      supportSize q+2=uniformMinimumTotalSupport m hm ε hε fixed :=
  by
    classical
    exact Nat.find_spec (uniform_witness_support_exists m hm ε hε fixed)

theorem uniformMinimumTotalSupport_le (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hw : UniformWitness m ε fixed a q B) :
    uniformMinimumTotalSupport m hm ε hε fixed ≤ supportSize q+2 :=
  by
    classical
    exact Nat.find_min' (uniform_witness_support_exists m hm ε hε fixed) ⟨a,q,B,hw,rfl⟩

theorem uniformMinimumTotalSupport_zero (m : ℕ) (hm : 2 ≤ m) (fixed : Bool) :
    uniformMinimumTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 (le_refl 0) fixed = m+2 := by
  obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m (by omega) 0 (by norm_num) fixed
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  obtain ⟨hq,ha,_,hnorm,hB,hb,hresp⟩ := hw
  have hrigid := bounded_two_anchor_minimum_share_rigidity hm (uniformTarget m (1/4)) q a
    (uniformTarget_positive m (1/4) (by norm_num)) (uniformTarget_mass m (by omega) (1/4))
    ha hq hnorm B hB hb hresp
  have hcard : supportSize q=m := by
    rw [hrigid.2.1]
    exact positive_target_full_support _ (uniformTarget_positive m (1/4) (by norm_num))
  omega

/-- Sharp-order total support complexity with the paper's explicit
    constants, for both minimum-share and fixed-share commitment classes. -/
theorem uniformMinimumTotalSupport_sharp (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (fixed : Bool) :
    Real.sqrt (3/1216)*min ((m : ℝ)+2) (1/Real.sqrt ε) ≤
      (uniformMinimumTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) fixed : ℝ) ∧
    (uniformMinimumTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) fixed : ℝ) ≤
      5*min ((m : ℝ)+2) (1/Real.sqrt ε) := by
  constructor
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m (by omega) ε (le_of_lt hε) fixed
    simp only [UniformWitness,Nat.cast_ofNat] at hw
    obtain ⟨hq,ha,_,hnorm,hB,hb,hresp⟩ := hw
    have hh := uniform_total_support_lower (by omega) q a hq ha hnorm B hB
      (fun i j => (hb i j).1) ε hε hresp
    have heq : (supportSize q : ℝ)+2 = (uniformMinimumTotalSupport m (by omega) ε (le_of_lt hε) fixed : ℝ) := by
      exact_mod_cast hcount
    rw [← heq]
    exact hh
  · obtain ⟨q,B,hq,hqm,hB,hb,hresp,_,hcount⟩ := uniform_sparse_upper_rate (m := m) (by omega) ε hε hε1
    have hw : UniformWitness m ε fixed (twoShares (3/4)) q B := by
      unfold UniformWitness
      norm_num only [Nat.cast_ofNat]
      refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,hresp⟩
      rw [hqm,Fin.sum_univ_two]
      norm_num [twoShares]
    have hle := uniformMinimumTotalSupport_le m (by omega) ε (le_of_lt hε) fixed (twoShares (3/4)) q B hw
    have hleR : (uniformMinimumTotalSupport m (by omega) ε (le_of_lt hε) fixed : ℝ) ≤ (supportSize q : ℝ)+2 := by
      exact_mod_cast hle
    exact le_trans hleR hcount

end
end SparseCompletion
