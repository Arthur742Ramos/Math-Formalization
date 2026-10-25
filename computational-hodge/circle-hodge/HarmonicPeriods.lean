module
public import CircleIntegrals
@[expose] public section

namespace ComputationalHodge.CircleHodge
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters

noncomputable def meanCochain (α : Coefficient) : Cochain Unit :=
  characterCochain circleRooting (mean α • circleCharacter)

theorem meanCochain_period (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    period p (meanCochain α)=mean α*(windingCharacter (traceClass p)).toAdd :=
  characterCochain_loop circleRooting (mean α • circleCharacter) p

theorem meanCochain_unit (α : Coefficient) : meanCochain α ()=mean α := by
  have h := meanCochain_period α (.single ())
  change meanCochain α ()=mean α*winding onceAround at h
  simpa only [winding_onceAround,mul_one] using h

theorem circle_exact_eq_bot : Exact circleSystem=⊥ := by
  apply le_antisymm
  · rintro ω ⟨f,rfl⟩
    change d0 circleSystem.toGeometricStepSystem f=0
    ext e
    exact sub_self (f 0)
  · exact bot_le

/-- A proved member of the existing actual finite harmonic-cochain subspace. -/
noncomputable def harmonicCochain (α : Coefficient) : Harmonic (geometricPresentation circleSystem) :=
  ⟨meanCochain α,characterCochain_closed circleRooting (mean α • circleCharacter),
    by rw [circle_exact_eq_bot,Submodule.bot_orthogonal_eq_top]; trivial⟩

theorem harmonicCochain_period (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    period p (harmonicCochain α)=mean α*(windingCharacter (traceClass p)).toAdd :=
  meanCochain_period α p

theorem analytic_computational_period (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) (L : C1Lift)
    (h : _root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p) :
    lineIntegral α L=period p (harmonicCochain α) := by
  rw [lineIntegral_eq_winding,harmonicCochain_period,h]

/-- Existence is proved; a smooth representative is not supplied as a bridge hypothesis. -/
theorem computational_smooth_realization (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p ∧
      lineIntegral α L=period p (harmonicCochain α) := by
  obtain ⟨L,hL⟩ := smooth_representative (traceClass p)
  exact ⟨L,hL,analytic_computational_period α p L hL⟩

theorem zero_harmonic_iff_exact (α : Coefficient) :
    harmonicCochain α=0 ↔ ExactCoefficient α := by
  constructor
  · intro h
    apply (mean_zero_iff_exact α).mp
    have hc := congrArg (fun h : Harmonic (geometricPresentation circleSystem) => h.val ()) h
    simpa [harmonicCochain,meanCochain_unit] using hc
  · intro h
    apply Subtype.ext
    ext e
    cases e
    change meanCochain α ()=0
    rw [meanCochain_unit,exact_mean_zero h]

theorem same_harmonic_iff_exact_difference (α β : Coefficient) :
    harmonicCochain α=harmonicCochain β ↔ ExactCoefficient (α-β) := by
  constructor
  · intro h
    apply (mean_zero_iff_exact _).mp
    rw [mean_sub]
    apply sub_eq_zero.mpr
    have hc := congrArg (fun h : Harmonic (geometricPresentation circleSystem) => h.val ()) h
    simpa [harmonicCochain,meanCochain_unit] using hc
  · intro h
    have hc := exact_mean_zero h
    rw [mean_sub] at hc
    apply Subtype.ext
    ext e
    cases e
    change meanCochain α ()=meanCochain β ()
    rw [meanCochain_unit,meanCochain_unit]
    exact sub_eq_zero.mp hc

theorem harmonicCochain_surjective : Function.Surjective harmonicCochain := by
  intro h
  refine ⟨constant (h.val ()),?_⟩
  apply Subtype.ext
  ext e
  cases e
  change meanCochain (constant (h.val ())) ()=h.val ()
  rw [meanCochain_unit,mean_constant]

theorem all_loop_integrals_zero_iff_exact (α : Coefficient) :
    (∀ L : C1Lift,lineIntegral α L=0) ↔ ExactCoefficient α := by
  constructor
  · intro h
    apply (mean_zero_iff_exact α).mp
    have h1 := h (straightLift 1)
    rw [lineIntegral_eq_mean_endpoint] at h1
    change mean α*(((1 : ℤ) : ℝ)*1)=0 at h1
    simpa only [Int.cast_one,one_mul,mul_one] using h1
  · exact fun h L => exact_lineIntegral_zero h L

theorem unique_computational_harmonic (α : Coefficient) :
    ∃! h : Harmonic (geometricPresentation circleSystem),
      ∀ (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) (L : C1Lift),
        _root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p →
          lineIntegral α L=period p h := by
  refine ⟨harmonicCochain α,analytic_computational_period α,?_⟩
  intro h hh
  obtain ⟨L,hL,hI⟩ := computational_smooth_realization α (.single ())
  have hp := (hh (.single ()) L hL).symm.trans hI
  apply Subtype.ext
  ext e
  cases e
  exact hp

end ComputationalHodge.CircleHodge
