module

public import LeadingKernel
public import BoundaryLeading

/-! Comparisons from genuine filtered quotient pages to actual vertical cohomology. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem leading_zero_of_boundary (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hdd : ImageKernel K (p - 1) q) (x : Filtered.cycles (filtered K) r p n)
    (hx : x.val ∈ Filtered.boundaries (filtered K) (r - 1) p n) :
    leadingClassMap K r p q n hn hr x = 0 := by
  obtain ⟨u, _, hu⟩ := hx.2
  have huf : ((total K).d (n - 1) n).hom u ∈ filtration K p n := by
    rw [hu]
    exact hx.1
  obtain ⟨b, hb⟩ := boundary_leading_exact K p q n hn hdd u huf
  change verticalClassMap K p q (leadingCycleMap K r p q n hn hr x) = 0
  apply (verticalClassMap_eq_zero_iff K p q _).mpr
  refine ⟨b, ?_⟩
  change incomingVertical K p q b = (projection K p q n).hom x.val
  rw [← hu]
  exact hb

theorem leading_zero_of_boundary_e1 (p q n : ℤ) (hn : p + q = n)
    (x : Filtered.cycles (filtered K) 1 p n)
    (hx : x.val ∈ Filtered.boundaries (filtered K) (1 - 1) p n) :
    leadingClassMap K 1 p q n hn (le_refl 1) x = 0 := by
  obtain ⟨u, hup, hu⟩ := hx.2
  have hup' : u ∈ filtration K p (n - 1) := by
    simp only [sub_self, sub_zero] at hup
    exact hup
  obtain ⟨b, hb⟩ := boundary_leading_exact_of_primitive_mem K p q n hn u hup'
  change verticalClassMap K p q (leadingCycleMap K 1 p q n hn (le_refl 1) x) = 0
  apply (verticalClassMap_eq_zero_iff K p q _).mpr
  refine ⟨b, ?_⟩
  change incomingVertical K p q b = (projection K p q n).hom x.val
  rw [← hu]
  exact hb

theorem leading_kills_denominator_of_boundary (r p q n : ℤ) (hn : p + q = n)
    (hr : 1 ≤ r)
    (hbzero : ∀ x : Filtered.cycles (filtered K) r p n,
      x.val ∈ Filtered.boundaries (filtered K) (r - 1) p n →
        leadingClassMap K r p q n hn hr x = 0) :
    (Filtered.denominator (filtered K) r p n).comap
      (Filtered.cycles (filtered K) r p n).subtype ≤
        LinearMap.ker (leadingClassMap K r p q n hn hr) := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hac : a ∈ Filtered.cycles (filtered K) r p n :=
    Filtered.denominator_le_cycles (filtered K) r p n
      ((show Filtered.cycles (filtered K) (r - 1) (p + 1) n ≤
        Filtered.denominator (filtered K) r p n from le_sup_left) ha)
  have hbc : b ∈ Filtered.cycles (filtered K) r p n :=
    Filtered.denominator_le_cycles (filtered K) r p n
      ((show Filtered.boundaries (filtered K) (r - 1) p n ≤
        Filtered.denominator (filtered K) r p n from le_sup_right) hb)
  have hx' : (⟨a, hac⟩ : Filtered.cycles (filtered K) r p n) + ⟨b, hbc⟩ = x :=
    Subtype.ext hab
  change leadingClassMap K r p q n hn hr x = 0
  rw [← hx', map_add, leadingClassMap_zero_of_next K r p q n hn hr ⟨a, hac⟩ ha.1,
    hbzero ⟨b, hbc⟩ hb, add_zero]

noncomputable def pageClassMap (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hdd : ImageKernel K (p - 1) q) :
    Filtered.Page (filtered K) r p n →ₗ[k] (K.X p).homology q :=
  ((Filtered.denominator (filtered K) r p n).comap
    (Filtered.cycles (filtered K) r p n).subtype).liftQ
      (leadingClassMap K r p q n hn hr)
      (leading_kills_denominator_of_boundary K r p q n hn hr
        (leading_zero_of_boundary K r p q n hn hr hdd))

/-- The first-page comparison is defined for every bicomplex, with no d'd'' hypothesis. -/
noncomputable def firstPageClassMap (p q n : ℤ) (hn : p + q = n) :
    Filtered.Page (filtered K) 1 p n →ₗ[k] (K.X p).homology q :=
  ((Filtered.denominator (filtered K) 1 p n).comap
    (Filtered.cycles (filtered K) 1 p n).subtype).liftQ
      (leadingClassMap K 1 p q n hn (le_refl 1))
      (leading_kills_denominator_of_boundary K 1 p q n hn (le_refl 1)
        (leading_zero_of_boundary_e1 K p q n hn))

@[simp]
theorem pageClassMap_quotient (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hdd : ImageKernel K (p - 1) q) (x : Filtered.cycles (filtered K) r p n) :
    pageClassMap K r p q n hn hr hdd (Filtered.quotient (filtered K) r p n x) =
      leadingClassMap K r p q n hn hr x := rfl

@[simp]
theorem firstPageClassMap_quotient (p q n : ℤ) (hn : p + q = n)
    (x : Filtered.cycles (filtered K) 1 p n) :
    firstPageClassMap K p q n hn (Filtered.quotient (filtered K) 1 p n x) =
      leadingClassMap K 1 p q n hn (le_refl 1) x := rfl

end AlgebraicHodgePilot.Column
