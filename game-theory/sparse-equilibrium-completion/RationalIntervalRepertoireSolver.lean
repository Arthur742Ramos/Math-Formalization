/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalPhysicalNecessity
@[expose] public section
namespace SparseCompletion

def rationalIntervalRepertoireAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Option ((Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) × (Fin m → Fin m → ℚ)) :=
  (rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R)).bind
    (fun x => (reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η).map (fun B => (x,B)))

theorem rational_interval_repertoire_algorithm_output {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,B)) :
    RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
      M r ρ η (intervalAux x) ∧ R.Satisfies (intervalPhysicalVector x) ∧
    reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η=some B := by
  unfold rationalIntervalRepertoireAlgorithm at h
  cases hs : rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) with
  | none => simp only [hs,Option.bind_none] at h; cases h
  | some y =>
    cases hb : reconstructRationalGap (rationalIntervalRecover lo (intervalV y) (intervalQ y))
      p (intervalQ y) M ρ η with
    | none => simp only [hs,Option.bind_some,hb,Option.map_none] at h; cases h
    | some C =>
      have he : (y,C)=(x,B) := Option.some.inj
        (by simpa only [hs,Option.bind_some,hb,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      have hf := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R y).mp
        (rational_lp_solve_sound _ _ y hs)
      exact ⟨(rational_interval_system_point loK hiK lo hi p M r ρ η y).mp hf.1,hf.2,hb⟩

theorem rational_interval_repertoire_algorithm_real_complete {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    ∃ x B, rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,B) := by
  obtain ⟨x,hx⟩ := rational_lp_real_complete _ _ hf
  have hp := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp
    (rational_lp_solve_sound _ _ x hx)
  have hpoint := (rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hp.1
  have hg := (rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hpoint).2.2
  obtain ⟨B,hB⟩ := rational_interval_gap_rational_completion _ lo hi _ p _ M r ρ η hM hη hlu hg
  exact ⟨x,B,by simp only [rationalIntervalRepertoireAlgorithm,hx,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion
