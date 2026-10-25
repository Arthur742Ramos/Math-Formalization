module

public import Harmonic

@[expose] public section
namespace ComputationalHodge
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E]

def componentSetoid (S : GeometricStepSystem A E) : Setoid A where
  r a b := Nonempty (GeometricTrace S a b)
  iseqv := ⟨fun a => ⟨.refl a⟩,
    fun ⟨p⟩ => ⟨.symm p⟩, fun ⟨p⟩ ⟨q⟩ => ⟨.trans p q⟩⟩

noncomputable def componentRoot (S : GeometricStepSystem A E) (a : A) : A :=
  Quotient.out (Quotient.mk (componentSetoid S) a)

noncomputable def rootTrace (S : GeometricStepSystem A E) (a : A) :
    GeometricTrace S (componentRoot S a) a :=
  Classical.choice (Quotient.exact (Quotient.out_eq (Quotient.mk (componentSetoid S) a)))

/-- A componentwise potential is constructed from actual trace integrals. -/
noncomputable def potential (S : GeometricStepSystem A E) (ω : Cochain E) (a : A) : ℝ :=
  period (rootTrace S a) ω

theorem period_cast_source {S : GeometricStepSystem A E} {a a' b : A}
    (h : a = a') (p : GeometricTrace S a' b) (ω : Cochain E) :
    period (h.symm ▸ p) ω = period p ω := by
  cases h
  rfl

theorem potential_d0_of_zero_periods (S : GeometricStepSystem A E) (ω : Cochain E)
    (hz : ∀ (a : A) (p : GeometricTrace S a a), period p ω = 0) :
    d0 S (potential S ω) = ω := by
  ext e
  have hr : componentRoot S (S.src e) = componentRoot S (S.tgt e) :=
    congrArg Quotient.out (Quotient.sound (⟨GeometricTrace.single e⟩ :
      Nonempty (GeometricTrace S (S.src e) (S.tgt e))))
  let q : GeometricTrace S (componentRoot S (S.src e)) (S.tgt e) :=
    hr.symm ▸ rootTrace S (S.tgt e)
  have hq : period q ω = period (rootTrace S (S.tgt e)) ω := by
    exact period_cast_source hr (rootTrace S (S.tgt e)) ω
  have h := hz (componentRoot S (S.src e))
    (.trans (.trans (rootTrace S (S.src e)) (.single e)) (.symm q))
  change (period (rootTrace S (S.src e)) ω + ω e) - period q ω = 0 at h
  rw [hq] at h
  change potential S ω (S.tgt e) - potential S ω (S.src e) = ω e
  dsimp [potential]
  linarith

variable [TopologicalSpace E] {S : ContinuousGeometricStepSystem A E}

/-- All loop periods vanish exactly for actual coboundaries. No connectivity
or ambient geometric-completeness hypothesis is inserted. -/
theorem exact_iff_zero_loop_periods (ω : Cochain E) :
    ω ∈ Exact S ↔ ∀ (a : A) (p : GeometricTrace S.toGeometricStepSystem a a), period p ω = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ a p
    rw [period_d0, sub_self]
  · intro hz
    exact ⟨potential S.toGeometricStepSystem ω,
      potential_d0_of_zero_periods S.toGeometricStepSystem ω hz⟩

theorem harmonic_determined_by_periods (P : ScopedGeometricRewritePresentation S)
    (h k : Harmonic P)
    (hperiod : ∀ (a : A) (p : GeometricTrace S.toGeometricStepSystem a a), period p h = period p k) :
    h = k := by
  have he : (h : Cochain E) - (k : Cochain E) ∈ Exact S := by
    apply (exact_iff_zero_loop_periods _).mpr
    intro a p
    rw [map_sub, hperiod, sub_self]
  have hz := harmonic_exact_zero P ((Harmonic P).sub_mem h.property k.property) he
  exact Subtype.ext (sub_eq_zero.mp hz)

theorem periodPairing_separates (P : ScopedGeometricRewritePresentation S) (c d : H1 P)
    (hp : ∀ (a : A) (p : PathClass P a a), periodPairing P a p c = periodPairing P a p d) :
    c = d := by
  induction c using Submodule.Quotient.induction_on with | _ ω =>
  induction d using Submodule.Quotient.induction_on with | _ η =>
  have he : (ω : Cochain E) - (η : Cochain E) ∈ Exact S := by
    apply (exact_iff_zero_loop_periods _).mpr
    intro a p
    rw [map_sub]
    exact sub_eq_zero.mpr (hp a (Quotient.mk _ p))
  exact (Submodule.Quotient.eq (Boundaries P)).mpr he

end ComputationalHodge
