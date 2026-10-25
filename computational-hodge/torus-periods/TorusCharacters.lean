module
public import TorusHarmonic
@[expose] public section

namespace ComputationalHodge.TorusPeriods
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
variable {E : Type} [finiteE : Fintype E] [topE : TopologicalSpace E]
  [discreteE : DiscreteTopology E] [decidableE : DecidableEq E]

omit finiteE topE discreteE decidableE in
theorem windingVector_zpow (g : FundamentalGroup (Torus E) 0) (n : ℤ) (e : E) :
    windingVector (g^n) e = (n : ℝ)*windingVector g e := by
  unfold windingVector
  rw [map_zpow,map_zpow]
  simp

/-- Finite products of integer powers of actual coordinate loops realize every
integer winding vector supported on a finite set. Membership retains a genuine trace witness. -/
theorem finite_winding_realization (s : Finset E) (z : E → ℤ) :
    ∃ g : representedGroup (torusSystem E) 0,
      ∀ j, windingVector g.val j = if j ∈ s then (z j : ℝ) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1,fun j => ?_⟩
    change windingVector (1 : FundamentalGroup (Torus E) 0) j = _
    rw [windingVector_one]
    simp
  | @insert e s he ih =>
    obtain ⟨g,hg⟩ := ih
    let k : representedGroup (torusSystem E) 0 := representedLoop (.single e)
    refine ⟨k^(z e)*g,fun j => ?_⟩
    change windingVector (k.val^(z e)*g.val) j = _
    rw [windingVector_mul,windingVector_zpow]
    change (z e : ℝ)*windingVector (traceClass (S := torusSystem E) (.single e)) j+
      windingVector g.val j = _
    rw [coordinate_winding,hg]
    by_cases hje : j=e
    · subst j
      simp [he]
    · simp [hje,Ne.symm hje]

/-- All ambient torus loop classes have actual finite computational representatives. -/
theorem every_ambient_class_represented (g : FundamentalGroup (Torus E) 0) :
    ∃ p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0, traceClass p=g := by
  classical
  have hi : ∀ e, ∃ n : ℤ, (n : ℝ)=windingVector g e :=
    fun e => circle_winding_integral (coordinateMap e g)
  choose z hz using hi
  obtain ⟨k,hk⟩ := finite_winding_realization Finset.univ z
  have h : k.val=g := windingVector_injective (by
    funext e
    simpa [hz] using hk e)
  exact k.property.imp (fun _ hp => hp.trans h)

theorem torus_represented_eq_top : representedGroup (torusSystem E) 0 = ⊤ := by
  apply top_unique
  intro g _
  exact every_ambient_class_represented g

/-- Reconstruction is exact on all ambient characters because coordinate traces
generate the entire ambient group, rather than just a stipulated presented group. -/
theorem ambientPeriod_reconstructed (χ : AmbientCharacters E) :
    ambientPeriod (reconstructed χ)=χ := by
  apply Subtype.ext
  funext g
  obtain ⟨p,rfl⟩ := every_ambient_class_represented g
  have h := reconstructed_period (ambientPeriod (reconstructed χ)) p
  rw [reconstructed_ambientPeriod] at h
  exact h.symm.trans (reconstructed_period χ p)

theorem ambientPeriod_loop (ω : Cochain E)
    (p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0) :
    (ambientPeriod ω).val (traceClass p)=period p ω := by
  have h := reconstructed_period (ambientPeriod ω) p
  rw [reconstructed_ambientPeriod] at h
  exact h.symm

noncomputable def ambientPeriodLinear : Cochain E →ₗ[ℝ] AmbientCharacters E where
  toFun := ambientPeriod
  map_add' ω η := by
    apply Subtype.ext
    funext g
    change (∑ e,(ω+η) e*windingVector g e) = _
    simp [ambientPeriod,add_mul,Finset.sum_add_distrib]
  map_smul' r ω := by
    apply Subtype.ext
    funext g
    change (∑ e,(r • ω) e*windingVector g e) = _
    simp [ambientPeriod,Finset.mul_sum,mul_assoc]

/-- The actual finite cochain space is linearly equivalent to all ordinary
algebraic real characters of the ambient torus fundamental group. -/
noncomputable def cochainAmbientEquiv : Cochain E ≃ₗ[ℝ] AmbientCharacters E :=
  LinearEquiv.ofBijective ambientPeriodLinear
    ⟨fun ω η h => (reconstructed_ambientPeriod ω).symm.trans
      ((congrArg reconstructed h).trans (reconstructed_ambientPeriod η)),
     fun χ => ⟨reconstructed χ,ambientPeriod_reconstructed χ⟩⟩

noncomputable def harmonicAmbientEquiv :
    Harmonic (geometricPresentation (torusSystem E)) ≃ₗ[ℝ] AmbientCharacters E :=
  LinearEquiv.ofBijective (ambientPeriodLinear.comp (Submodule.subtype _))
    ⟨fun _ _ hh => Subtype.ext (cochainAmbientEquiv.injective hh),
     fun χ => ⟨harmonicCoefficients (reconstructed χ),ambientPeriod_reconstructed χ⟩⟩

theorem harmonicAmbientEquiv_loop
    (h : Harmonic (geometricPresentation (torusSystem E)))
    (p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0) :
    (harmonicAmbientEquiv h).val (traceClass p)=period p h :=
  ambientPeriod_loop (h : Cochain E) p

theorem ambient_character_formula (χ : AmbientCharacters E)
    (g : FundamentalGroup (Torus E) 0) :
    χ.val g = ∑ e,χ.val (traceClass (S := torusSystem E) (.single e))*windingVector g e := by
  have h := congrArg (fun ψ : AmbientCharacters E => ψ.val g) (ambientPeriod_reconstructed χ)
  change (∑ e,reconstructed χ e*windingVector g e)=χ.val g at h
  simpa only [reconstructed_coordinate] using h.symm

theorem cochainAmbientEquiv_inverse_coordinate (χ : AmbientCharacters E) (e : E) :
    (cochainAmbientEquiv.symm χ) e = χ.val (traceClass (S := torusSystem E) (.single e)) := by
  have h := reconstructed_ambientPeriod (cochainAmbientEquiv.symm χ)
  change reconstructed (cochainAmbientEquiv (cochainAmbientEquiv.symm χ)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrArg (fun ω : Cochain E => ω e) h).symm.trans (reconstructed_coordinate χ e)

theorem unique_harmonic_ambient_character (χ : AmbientCharacters E) :
    ∃! h : Harmonic (geometricPresentation (torusSystem E)),
      ∀ g, (harmonicAmbientEquiv h).val g=χ.val g := by
  refine ⟨harmonicAmbientEquiv.symm χ,fun g => ?_,fun h hh => ?_⟩
  · rw [LinearEquiv.apply_symm_apply]
  · apply harmonicAmbientEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (funext hh)

theorem unique_harmonic_loop_periods (χ : AmbientCharacters E) :
    ∃! h : Harmonic (geometricPresentation (torusSystem E)),
      ∀ p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0,
        period p h=χ.val (traceClass p) := by
  refine ⟨harmonicAmbientEquiv.symm χ,fun p => ?_,fun h hh => ?_⟩
  · rw [← harmonicAmbientEquiv_loop,LinearEquiv.apply_symm_apply]
  · apply harmonicAmbientEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext g
    obtain ⟨p,rfl⟩ := every_ambient_class_represented g
    exact (harmonicAmbientEquiv_loop h p).trans (hh p)

/-- The zero-dimensional torus needs no nonempty-index assumption. -/
theorem empty_index_character_zero [IsEmpty E] (χ : AmbientCharacters E)
    (g : FundamentalGroup (Torus E) 0) : χ.val g=0 := by
  rw [ambient_character_formula]
  simp

end ComputationalHodge.TorusPeriods
