/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.CoreLower

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem two_core_anchor_shift {ι : Type*} [Fintype ι] (D : ι → Fin (2 : ℕ) → ℝ)
    (B : ι → ι → ℝ) (q : ι → ℝ) (u τ : ℝ) :
    response (blockMatrix (twoCore (u-(((8 : ℕ) : ℝ)/(3 : ℕ))*τ)) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=
      response (blockMatrix (twoCore u) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)-τ ∧
    response (blockMatrix (twoCore (u-(((8 : ℕ) : ℝ)/(3 : ℕ))*τ)) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)=
      response (blockMatrix (twoCore u) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)+τ := by
  norm_num only [Nat.cast_ofNat] at *
  constructor <;> rw [block_response_anchor,block_response_anchor] <;>
    simp only [anchorResponse,Fin.sum_univ_two,twoCore,twoShares] <;> norm_num <;> ring

theorem core_observation_adjustment (u d δ : ℝ) (hu1 : u ≤ 1)
    (hd : 0 ≤ d) (hdu : (((8 : ℕ) : ℝ)/(3 : ℕ))*d ≤ u) (hδ : 0 ≤ δ) :
    let u' := u-(((8 : ℕ) : ℝ)/(3 : ℕ))*min d ((((3 : ℕ) : ℝ)/(8 : ℕ))*δ)
    ∀ i j, ClippedObservation (twoCore u i j) δ (twoCore u' i j) := by
  norm_num only [Nat.cast_ofNat] at *
  have hτ0 : 0 ≤ min d ((3/8)*δ) := le_min hd (by positivity)
  have hτd := min_le_left d ((3/8)*δ)
  have hτδ := min_le_right d ((3/8)*δ)
  have hnew0 : 0 ≤ u-(8/3)*min d ((3/8)*δ) := by nlinarith
  have hnew1 : u-(8/3)*min d ((3/8)*δ) ≤ 1 := by nlinarith
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoCore,ClippedObservation,abs_le] <;>
    (repeat' constructor) <;> linarith [abs_of_nonneg hτ0]

/-- A nonnegative anchor error can be absorbed by moving only the bounded
    anchor-core observation inside its clipped interval. -/
theorem uniform_core_adjust {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ) (d ε δ : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hmass : ∑ j, q j=1/(4 : ℕ)) (hB : IsSkew B)
    (hb : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) (hd : 0 ≤ d)
    (hβ : d ≤ scoreMoment (uniformTarget m (1/(4 : ℕ))) (exposingWeight (uniformTarget m (1/(4 : ℕ))) (1/(4 : ℕ))))
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (heff : d ≤ ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)
    (h0 : response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d)
    (h1 : response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d)
    (hrows : ∀ j, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0) :
    ∃ u, UniformCoreWitness m ε δ q u B := by
  norm_num only [Nat.cast_ofNat] at *
  let qstar := uniformTarget m (1/4)
  let u := uniformCoreValue m
  let τ := min d ((3/8)*δ)
  have hobs := two_anchor_observed_bounds hm qstar
    (fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)) (uniformTarget_mass m hm (1/4))
  have hu1 : u ≤ 1 := by simpa [u,uniformCoreValue,twoCore,qstar] using (hobs.1 0 1).2
  have hdu : (8/3)*d ≤ u := by
    dsimp [u,uniformCoreValue]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hclip := core_observation_adjustment u d δ hu1 hd hdu hδ
  norm_num only [Nat.cast_ofNat] at hclip
  refine ⟨u-(8/3)*τ,?_⟩
  unfold UniformCoreWitness UniformIntervalWitness
  norm_num only [Nat.cast_ofNat]
  refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,twoCore_skew _,hB,hclip,?_,hb,?_⟩
  · rw [hmass,Fin.sum_univ_two]
    norm_num [twoShares]
  · intro j h
    exact ⟨(hobs.2 j h).1,(hobs.2 j h).2,by simpa using hδ⟩
  · intro v
    cases v with
    | inl h =>
      have hshift := two_core_anchor_shift (rigidityCross qstar) B q u τ
      norm_num only [Nat.cast_ofNat] at hshift
      change response (blockMatrix (twoCore u) (rigidityCross qstar) B)
        (blockWeights (twoShares (3/4)) q) (.inl 0)=d at h0
      change response (blockMatrix (twoCore u) (rigidityCross qstar) B)
        (blockWeights (twoShares (3/4)) q) (.inl 1)= -d at h1
      rw [h0,h1] at hshift
      have hτd : τ ≤ d := min_le_left _ _
      have hτ : d-τ ≤ ε := by
        dsimp only [τ]
        rcases le_total d ((3/8)*δ) with hh | hh
        · rw [min_eq_left hh]
          linarith
        · rw [min_eq_right hh]
          linarith
      fin_cases h
      · exact le_of_eq_of_le hshift.1 hτ
      · exact le_of_eq_of_le hshift.2 (by linarith)
    | inr j =>
      rw [block_response_residual]
      have hh := hrows j
      rw [block_response_residual] at hh
      linarith

end
end SparseCompletion
