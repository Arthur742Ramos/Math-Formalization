module

public import Integration

/-! Actual cycles, boundaries, quotient pages and induced differentials of a filtered complex. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Filtered

variable {k : Type} [Field k]

/-- A decreasing filtration by subcomplexes of an actual cochain complex.
Only filtration laws are data; no page computation or degeneration is assumed. -/
structure Filtration (C : CochainComplex (ModuleCat k) ℤ) where
  F : (p n : ℤ) → Submodule k (C.X n)
  antitone (n : ℤ) : Antitone (fun p => F p n)
  preserves (p n m : ℤ) : F p n ≤ (F p m).comap (C.d n m).hom

variable {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)

def cycles (r p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ (F.F (p + r) (n + 1)).comap (C.d n (n + 1)).hom

def boundaries (r p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ (F.F (p - r) (n - 1)).map (C.d (n - 1) n).hom

def denominator (r p n : ℤ) : Submodule k (C.X n) :=
  cycles F (r - 1) (p + 1) n ⊔ boundaries F (r - 1) p n

theorem differential_squared (n : ℤ) (x : C.X n) :
    (C.d (n + 1) (n + 1 + 1)).hom ((C.d n (n + 1)).hom x) = 0 :=
  congrArg (fun f => f.hom x) (C.d_comp_d n (n + 1) (n + 1 + 1))

theorem boundary_closed (r p n : ℤ) {x : C.X n}
    (hx : x ∈ boundaries F r p n) : (C.d n (n + 1)).hom x = 0 := by
  obtain ⟨u, _, hu⟩ := hx.2
  rw [← hu]
  exact congrArg (fun f => f.hom u) (C.d_comp_d (n - 1) n (n + 1))

theorem denominator_le_cycles (r p n : ℤ) :
    denominator F r p n ≤ cycles F r p n := by
  apply sup_le
  · intro x hx
    refine ⟨F.antitone n (by lia) hx.1, ?_⟩
    have h : (p + 1) + (r - 1) = p + r := by lia
    simpa only [h] using hx.2
  · intro x hx
    exact ⟨hx.1, by change (C.d n (n + 1)).hom x ∈ F.F (p + r) (n + 1)
                    rw [boundary_closed F (r - 1) p n hx]
                    exact (F.F (p + r) (n + 1)).zero_mem⟩

/-- The standard filtered-complex quotient, retaining the actual cycle condition. -/
abbrev Page (r p n : ℤ) :=
  cycles F r p n ⧸ (denominator F r p n).comap (cycles F r p n).subtype

def differentialOnCycles (r p n : ℤ) :
    cycles F r p n →ₗ[k] cycles F r (p + r) (n + 1) :=
  ((C.d n (n + 1)).hom.comp (cycles F r p n).subtype).codRestrict _ fun x =>
    ⟨x.property.2, by
      change (C.d (n + 1) (n + 1 + 1)).hom ((C.d n (n + 1)).hom x.val) ∈ F.F (p + r + r) (n + 1 + 1)
      rw [differential_squared n x.val]
      exact (F.F (p + r + r) (n + 1 + 1)).zero_mem⟩

theorem differential_denominator (r p n : ℤ)
    (x : cycles F r p n)
    (hx : x ∈ (denominator F r p n).comap (cycles F r p n).subtype) :
    differentialOnCycles F r p n x ∈
      (denominator F r (p + r) (n + 1)).comap (cycles F r (p + r) (n + 1)).subtype := by
  change (C.d n (n + 1)).hom x.val ∈ denominator F r (p + r) (n + 1)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  change a + b = x.val at hab
  rw [← hab, map_add, boundary_closed F (r - 1) p n hb, add_zero]
  apply (le_sup_right : boundaries F (r - 1) (p + r) (n + 1) ≤
    denominator F r (p + r) (n + 1))
  change (C.d n (n + 1)).hom a ∈ boundaries F (r - 1) (p + r) (n + 1)
  refine ⟨?_, ?_⟩
  · have h : p + 1 + (r - 1) = p + r := by lia
    have hh : (C.d n (n + 1)).hom a ∈ F.F (p + 1 + (r - 1)) (n + 1) := ha.2
    rw [h] at hh
    exact hh
  · have h : p + r - (r - 1) = p + 1 := by lia
    rw [show n + 1 - 1 = n by lia, h]
    exact ⟨a, ha.1, rfl⟩

/-- The actual total differential descended to the standard filtered quotient. -/
def differential (r p n : ℤ) :
    Page F r p n →ₗ[k] Page F r (p + r) (n + 1) :=
  (denominator F r p n).comap (cycles F r p n).subtype |>.liftQ
    (((denominator F r (p + r) (n + 1)).comap
      (cycles F r (p + r) (n + 1)).subtype).mkQ.comp (differentialOnCycles F r p n))
    (by
      intro x hx
      change _ = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (differential_denominator F r p n x hx))

def quotient (r p n : ℤ) : cycles F r p n →ₗ[k] Page F r p n :=
  ((denominator F r p n).comap (cycles F r p n).subtype).mkQ

theorem quotient_surjective (r p n : ℤ) : Function.Surjective (quotient F r p n) :=
  Submodule.mkQ_surjective _

@[simp]
theorem differential_quotient (r p n : ℤ) (x : cycles F r p n) :
    differential F r p n (quotient F r p n x) =
      quotient F r (p + r) (n + 1) (differentialOnCycles F r p n x) := rfl

theorem page_differential_squared (r p n : ℤ) :
    (differential F r (p + r) (n + 1)).comp (differential F r p n) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := quotient_surjective F r p n x
  simp only [LinearMap.comp_apply, differential_quotient]
  have h : differentialOnCycles F r (p + r) (n + 1)
      (differentialOnCycles F r p n z) = 0 := by
    apply Subtype.ext
    exact differential_squared n z.val
  rw [h, map_zero]
  rfl

end AlgebraicHodgePilot.Filtered
