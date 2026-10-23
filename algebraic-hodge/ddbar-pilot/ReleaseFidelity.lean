module

public import E1Degeneration

/-! Canonical transition coverage and finite, exhaustive, separated abutment filtration. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Filtered

variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)

theorem cycles_succ_le (r p n : ℤ) : cycles F (r + 1) p n ≤ cycles F r p n := by
  intro x hx
  exact ⟨hx.1, F.antitone (n + 1) (show p + r ≤ p + (r + 1) by lia -abstractProof) hx.2⟩

theorem cohomologyFiltration_eq_top_of_top (p n : ℤ) (hF : F.F p n = ⊤) :
    cohomologyFiltration F p n = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro c
  obtain ⟨z, hz⟩ := cohomologyClassMap_surjective C n c
  refine ⟨⟨z.val, ?_, z.property⟩, ?_⟩
  · rw [hF]
    trivial
  · exact hz

theorem cohomologyFiltration_eq_bot_of_bot (p n : ℤ) (hF : F.F p n = ⊥) :
    cohomologyFiltration F p n = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro _ ⟨z, rfl⟩
  have hzval : z.val = 0 := by
    have hz := z.property.1
    rw [hF] at hz
    exact hz
  have hz : z = 0 := Subtype.ext hzval
  change closedClassMap F p n z = 0
  rw [hz, map_zero]

end AlgebraicHodgePilot.Filtered

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

/-- Every next-page cycle gives the standard recurrence class, without a separately
assumed membership in the preceding cycle submodule. -/
theorem associatedSequence_transition_next (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q : ℤ) (hr : 1 ≤ r)
    (x : Filtered.cycles (filtered K) (r + 1) p (p + q)) :
    ((associatedSequence K hdd).iso r (r + 1) (p, q) rfl hr).hom
      ((zeroPageHomologyIso K hdd r hr (p, q)).inv
        (Filtered.quotient (filtered K) r p (p + q)
          ⟨x.val, Filtered.cycles_succ_le (filtered K) r p (p + q) x.property⟩)) =
      Filtered.quotient (filtered K) (r + 1) p (p + q) x :=
  associatedSequence_transition K hdd r (r + 1) rfl hr p q x.val
    (Filtered.cycles_succ_le (filtered K) r p (p + q) x.property) x.property

/-- The common-representative recurrence rule covers every next-page class. -/
theorem associatedSequence_transition_covers (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q : ℤ) (hr : 1 ≤ r)
    (c : Filtered.Page (filtered K) (r + 1) p (p + q)) :
    ∃ x : Filtered.cycles (filtered K) (r + 1) p (p + q),
      Filtered.quotient (filtered K) (r + 1) p (p + q) x = c ∧
      ((associatedSequence K hdd).iso r (r + 1) (p, q) rfl hr).hom
        ((zeroPageHomologyIso K hdd r hr (p, q)).inv
          (Filtered.quotient (filtered K) r p (p + q)
            ⟨x.val, Filtered.cycles_succ_le (filtered K) r p (p + q) x.property⟩)) = c := by
  obtain ⟨x, hx⟩ := Filtered.quotient_surjective (filtered K) (r + 1) p (p + q) c
  exact ⟨x, hx, (associatedSequence_transition_next K hdd r p q hr x).trans hx⟩

theorem cohomologyFiltration_eq_top (L U : ℤ) (hs : HorizontalSupport K L U)
    (p n : ℤ) (hp : p ≤ L) : Filtered.cohomologyFiltration (filtered K) p n = ⊤ :=
  Filtered.cohomologyFiltration_eq_top_of_top (filtered K) p n
    (filtration_eq_top K L U hs p n hp)

theorem cohomologyFiltration_eq_bot (L U : ℤ) (hs : HorizontalSupport K L U)
    (p n : ℤ) (hp : U < p) : Filtered.cohomologyFiltration (filtered K) p n = ⊥ :=
  Filtered.cohomologyFiltration_eq_bot_of_bot (filtered K) p n
    (filtration_eq_bot K L U hs p n hp)

/-- The actual induced filtration on total cohomology is exhaustive and separated. -/
theorem cohomologyFiltration_exhaustive_separated (L U : ℤ) (hs : HorizontalSupport K L U)
    (n : ℤ) :
    (⨆ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n) = ⊤ ∧
    (⨅ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n) = ⊥ := by
  constructor
  · apply top_unique
    calc
      ⊤ = Filtered.cohomologyFiltration (filtered K) L n :=
        (cohomologyFiltration_eq_top K L U hs L n (le_refl L)).symm
      _ ≤ ⨆ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n :=
        le_iSup (fun p : ℤ => Filtered.cohomologyFiltration (filtered K) p n) L
  · apply bot_unique
    calc
      (⨅ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n) ≤
          Filtered.cohomologyFiltration (filtered K) (U + 1) n :=
        iInf_le (fun p : ℤ => Filtered.cohomologyFiltration (filtered K) p n) (U + 1)
      _ = ⊥ := cohomologyFiltration_eq_bot K L U hs (U + 1) n (by lia -abstractProof)

/-- Transport along proved equality of numerator and denominator preserves the
class of each actual representative. This generic lemma keeps transport opaque. -/
theorem quotient_cast_class {M : Type} [AddCommGroup M] [Module k M]
    (A B S T : Submodule k M) (hA : A = B) (hD : S = T)
    (he : ModuleCat.of k (A ⧸ S.comap A.subtype) = ModuleCat.of k (B ⧸ T.comap B.subtype))
    (x : M) (hx : x ∈ A) (hx' : x ∈ B) :
    (eqToIso he).hom ((S.comap A.subtype).mkQ ⟨x, hx⟩) =
      (T.comap B.subtype).mkQ ⟨x, hx'⟩ := by
  subst B T
  have hh : he = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

theorem stablePageIso_quotient (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L)
    (x : Filtered.closedCycles (filtered K) p n) :
    (stablePageIso K L U hs r p n hu hl).hom
      (Filtered.quotient (filtered K) r p n (Filtered.closedToCycles (filtered K) r p n x)) =
      Filtered.infinityQuotient (filtered K) p n x := by
  exact quotient_cast_class (Filtered.cycles (filtered K) r p n)
    (Filtered.closedCycles (filtered K) p n) (Filtered.denominator (filtered K) r p n)
    (Filtered.closedDenominator (filtered K) p n) (cycles_stable K L U hs r p n hu)
    (denominator_stable K L U hs r p n hu hl) _ x.val
    (Filtered.closedCycles_le_cycles (filtered K) r p n x.property) x.property

theorem boundedStableGradedIso_closed (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L)
    (x : Filtered.closedCycles (filtered K) p n) :
    (boundedStableGradedIso K L U hs r p n hu hl).hom
      (Filtered.quotient (filtered K) r p n (Filtered.closedToCycles (filtered K) r p n x)) =
      Filtered.closedToGraded (filtered K) p n x := by
  change (Filtered.infinityGradedIso (filtered K) p n).hom
    ((stablePageIso K L U hs r p n hu hl).hom _) = _
  rw [stablePageIso_quotient, Filtered.infinityGradedIso_quotient]

/-- The degeneration comparison and the bounded stabilization comparison agree
as actual morphisms to associated graded total cohomology. -/
theorem boundedStableGradedIso_eq_pageToGradedIso (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hu : U < p + r) (hl : p - r + 1 ≤ L) :
    (boundedStableGradedIso K L U hs r p n hu hl).hom =
      (pageToGradedIso K hdd r p q n hn hr).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := exists_closed_page_representative K hdd r p q n hn hr c
  rw [boundedStableGradedIso_closed, pageToGradedIso_closed]

end AlgebraicHodgePilot.Column
