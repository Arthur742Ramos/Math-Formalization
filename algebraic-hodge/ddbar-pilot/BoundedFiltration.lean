module

public import ColumnFiltration
public import FilteredInfinity

/-! Finite horizontal support makes the actual column filtration finite and its quotient pages stable. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

/-- Actual vanishing of all components outside a finite interval of columns. -/
def HorizontalSupport (L U : ℤ) : Prop :=
  ∀ p q, p < L ∨ U < p → Subsingleton ((K.X p).X q)

def RectangularSupport (L U B T : ℤ) : Prop :=
  ∀ p q, p < L ∨ U < p ∨ q < B ∨ T < q → Subsingleton ((K.X p).X q)

theorem rectangularSupport_horizontal (L U B T : ℤ) (hs : RectangularSupport K L U B T) :
    HorizontalSupport K L U := by
  intro p q hp
  exact hs p q (hp.elim Or.inl (fun h => Or.inr (Or.inl h)))

theorem filtration_eq_bot (L U : ℤ) (hs : HorizontalSupport K L U)
    (p n : ℤ) (hp : U < p) : filtration K p n = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun ha => ?_
  rintro _ ⟨x, rfl⟩
  have hx : x = 0 := @Subsingleton.elim _ (hs a b (Or.inr (by lia -abstractProof))) x 0
  simp [hx]

theorem filtration_eq_top (L U : ℤ) (hs : HorizontalSupport K L U)
    (p n : ℤ) (hp : p ≤ L) : filtration K p n = ⊤ := by
  let f : (total K).X n ⟶ ModuleCat.of k ((total K).X n ⧸ filtration K p n) :=
    ModuleCat.ofHom (filtration K p n).mkQ
  have hf : f = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    by_cases ha : p ≤ a
    · exact (Submodule.Quotient.mk_eq_zero _).mpr
        (inclusion_mem_filtration K p a b n hab ha x)
    · have hx : x = 0 := @Subsingleton.elim _ (hs a b (Or.inl (by lia -abstractProof))) x 0
      simp [hx]
  apply top_unique
  intro x _
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact congrArg (fun g => g.hom x) hf

theorem cycles_stable (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hr : U < p + r) :
    Filtered.cycles (filtered K) r p n = Filtered.closedCycles (filtered K) p n := by
  unfold Filtered.cycles Filtered.closedCycles
  change filtration K p n ⊓ (filtration K (p + r) (n + 1)).comap _ = _
  rw [filtration_eq_bot K L U hs (p + r) (n + 1) hr]
  rfl

theorem boundaries_stable (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hr : p - r ≤ L) :
    Filtered.boundaries (filtered K) r p n = Filtered.closedBoundaries (filtered K) p n := by
  unfold Filtered.boundaries Filtered.closedBoundaries
  change filtration K p n ⊓ (filtration K (p - r) (n - 1)).map _ = _
  rw [filtration_eq_top K L U hs (p - r) (n - 1) hr, Submodule.map_top]
  rfl

theorem denominator_stable (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) :
    Filtered.denominator (filtered K) r p n = Filtered.closedDenominator (filtered K) p n := by
  unfold Filtered.denominator Filtered.closedDenominator
  rw [cycles_stable K L U hs (r - 1) (p + 1) n (by lia -abstractProof),
    boundaries_stable K L U hs (r - 1) p n (by lia -abstractProof)]

/-- Eventual pages are the stable quotient by equality of their actual numerator and denominator. -/
noncomputable def stablePageIso (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) :
    ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅
      ModuleCat.of k (Filtered.InfinityPage (filtered K) p n) :=
  eqToIso (by
    unfold Filtered.Page Filtered.InfinityPage
    rw [cycles_stable K L U hs r p n hu, denominator_stable K L U hs r p n hu hl])

theorem eventually_stable (L U : ℤ) (hs : HorizontalSupport K L U) (p n : ℤ) :
    ∃ R : ℤ, 1 ≤ R ∧ ∀ r : ℤ, R ≤ r →
      Filtered.cycles (filtered K) r p n = Filtered.closedCycles (filtered K) p n ∧
      Filtered.denominator (filtered K) r p n = Filtered.closedDenominator (filtered K) p n := by
  refine ⟨max 1 (max (U - p + 1) (p - L + 1)), le_max_left _ _, ?_⟩
  intro r hr
  have hu : U < p + r := by omega
  have hl : p - r + 1 ≤ L := by omega
  exact ⟨cycles_stable K L U hs r p n hu, denominator_stable K L U hs r p n hu hl⟩

end AlgebraicHodgePilot.Column
