/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Total rational Fourier–Motzkin solve plus explicit residual reconstruction. -/
module
public import ProtectedSources.RationalIntervalPack
@[expose] public section
namespace SparseCompletion

def rationalIntervalAlgorithm {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) : Option ((Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) ×
      (Fin m → Fin m → ℚ)) :=
  (rationalLPSolve _ (rationalIntervalSystem loK hiK lo hi p M r ρ η)).bind (fun x =>
    (reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η).map (fun B => (x,B)))

theorem rational_interval_lp_feasible_iff {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) :
    (∃ x, (rationalIntervalSystem loK hiK lo hi p M r ρ η).Satisfies x) ↔
    ∃ q V K, (∀ a b, K a b= -K b a) ∧
      (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨intervalQ x,intervalV x,intervalK x,
      rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _
        ((rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hx)⟩
  · rintro ⟨q,V,K,h⟩
    obtain ⟨A,hA⟩ := (rational_interval_point_epigraph_iff loK hiK lo hi V K p q M r ρ η).mp h
    refine ⟨intervalPack q V K A,(rational_interval_system_point loK hiK lo hi p M r ρ η _).mpr ?_⟩
    simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hA

theorem rational_interval_algorithm_output {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (h : rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B)) :
    RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
      M r ρ η (intervalAux x) ∧
    reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η=some B := by
  unfold rationalIntervalAlgorithm at h
  cases hs : rationalLPSolve _ (rationalIntervalSystem loK hiK lo hi p M r ρ η) with
  | none => simp only [hs,Option.bind_none] at h; cases h
  | some y =>
    cases hb : reconstructRationalGap (rationalIntervalRecover lo (intervalV y) (intervalQ y))
      p (intervalQ y) M ρ η with
    | none => simp only [hs,Option.bind_some,hb,Option.map_none] at h; cases h
    | some C =>
      have he : (y,C)=(x,B) := Option.some.inj
        (by simpa only [hs,Option.bind_some,hb,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact ⟨(rational_interval_system_point loK hiK lo hi p M r ρ η y).mp
        (rational_lp_solve_sound _ _ y hs),hb⟩

theorem rational_interval_algorithm_complete {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ q V K, (∀ a b, K a b= -K b a) ∧
      (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    ∃ x B, rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B) := by
  obtain ⟨x,hx⟩ := rational_lp_solve_complete _ _
    ((rational_interval_lp_feasible_iff loK hiK lo hi p M r ρ η).mpr hf)
  have hp := (rational_interval_system_point loK hiK lo hi p M r ρ η x).mp
    (rational_lp_solve_sound _ _ x hx)
  have hg := (rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hp).2.2
  obtain ⟨B,hB⟩ := rational_interval_gap_rational_completion _ lo hi _ p _ M r ρ η hM hη hlu hg
  exact ⟨x,B,by simp only [rationalIntervalAlgorithm,hx,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion
