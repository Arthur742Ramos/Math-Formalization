/- AI-assisted formalization under the repository Apache-2.0 license.
Actual rational interval recovery and finite-support search. No polynomial cost. -/
module
public import ProtectedSources.RationalIntervalSparseReduction
@[expose] public section
namespace SparseCompletion

abbrev RationalSparseIntervalData (k m : ℕ) :=
  (Fin m → ℚ) × ((Fin k → Fin k → ℚ) ×
    ((Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ)))

def rationalIntervalSparseAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Option (RationalSparseIntervalData k m) :=
  (rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R)).bind
    (fun x =>
      let K := intervalK x
      let D := rationalIntervalRecover lo (intervalV x) (intervalQ x)
      (rationalSparseGapAlgorithm K D p M r ρ η (rationalFrozenPhysicalSystem K D R)).map
        (fun w => (w.1,(K,(D,w.2)))))

theorem rational_interval_sparse_algorithm_origin {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (q : Fin m → ℚ) (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalSparseAlgorithm loK hiK lo hi p M r ρ η R=some (q,(K,(D,B)))) :
    ∃ x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ,
      RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
        M r ρ η (intervalAux x) ∧ R.Satisfies (intervalPhysicalVector x) ∧
      K=intervalK x ∧ D=rationalIntervalRecover lo (intervalV x) (intervalQ x) ∧
      rationalSparseGapAlgorithm K D p M r ρ η (rationalFrozenPhysicalSystem K D R)=some (q,B) := by
  unfold rationalIntervalSparseAlgorithm at hout
  cases hx : rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) with
  | none => simp only [hx,Option.bind_none] at hout; cases hout
  | some x =>
    cases hs : rationalSparseGapAlgorithm (intervalK x)
      (rationalIntervalRecover lo (intervalV x) (intervalQ x)) p M r ρ η
      (rationalFrozenPhysicalSystem (intervalK x)
        (rationalIntervalRecover lo (intervalV x) (intervalQ x)) R) with
    | none => simp only [hx,Option.bind_some,hs,Option.map_none] at hout; cases hout
    | some w =>
      have he : (w.1,(intervalK x,(rationalIntervalRecover lo (intervalV x) (intervalQ x),w.2)))=
          (q,(K,(D,B))) := Option.some.inj
        (by simpa only [hx,Option.bind_some,hs,Option.map_some] using hout)
      obtain ⟨hqw,hrest⟩ := Prod.mk.inj he
      obtain ⟨hK,hrest⟩ := Prod.mk.inj hrest
      obtain ⟨hD,hB⟩ := Prod.mk.inj hrest
      have hp := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp
        (rational_lp_solve_sound _ _ x hx)
      refine ⟨x,(rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hp.1,
        hp.2,hK.symm,hD.symm,?_⟩
      have hw : w=(q,B) := Prod.ext hqw hB
      simpa only [hK,hD,hw] using hs

theorem rational_interval_sparse_algorithm_real_complete {k m : ℕ} {I : Type} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    ∃ w, rationalIntervalSparseAlgorithm loK hiK lo hi p M r ρ η R=some w := by
  obtain ⟨x,hx⟩ := rational_lp_real_complete _ _ hf
  have hp := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp
    (rational_lp_solve_sound _ _ x hx)
  obtain ⟨q,B,hq⟩ := rational_interval_sparse_reduction loK hiK lo hi p M r ρ η R x hM hη hlu
    ((rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hp.1) hp.2
  exact ⟨(q,(intervalK x,(rationalIntervalRecover lo (intervalV x) (intervalQ x),B))),by
    simp only [rationalIntervalSparseAlgorithm,hx,Option.bind_some,hq,Option.map_some]⟩

end SparseCompletion
