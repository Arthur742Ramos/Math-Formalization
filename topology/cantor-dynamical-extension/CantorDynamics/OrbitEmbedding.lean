module
public import KnasterReichbach.Extension
public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Basic.Denumerable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Tactic

public section
namespace CantorDynamics

abbrev CantorSpace := ℕ → Bool
abbrev ShiftSpace := ℤ → CantorSpace

/-- The two-sided shift, with the usual product topology. -/
@[expose] def shift : ShiftSpace ≃ₜ ShiftSpace where
  toFun x i := x (i + 1)
  invFun x i := x (i - 1)
  left_inv x := by funext i; change x (i - 1 + 1) = x i; simp
  right_inv x := by funext i; change x (i + 1 - 1) = x i; simp
  continuous_toFun := continuous_pi fun i => continuous_apply (i + 1)
  continuous_invFun := continuous_pi fun i => continuous_apply (i - 1)

@[simp] theorem shift_apply (x : ShiftSpace) (i : ℤ) : shift x i = x (i + 1) := rfl

/-- All positive and negative iterates of the prescribed dynamics. -/
def orbitEmbedding {A : Set CantorSpace} (f : A ≃ₜ A) (p : A) : ShiftSpace :=
  fun i => ((f ^ i) p).val

theorem continuous_orbitEmbedding {A : Set CantorSpace} (f : A ≃ₜ A) :
    Continuous (orbitEmbedding f) :=
  continuous_pi fun i => continuous_subtype_val.comp (f ^ i).continuous

theorem orbitEmbedding_injective {A : Set CantorSpace} (f : A ≃ₜ A) :
    Function.Injective (orbitEmbedding f) := by
  intro p q hpq
  apply Subtype.ext
  simpa [orbitEmbedding] using congrFun hpq 0

theorem shift_orbitEmbedding {A : Set CantorSpace} (f : A ≃ₜ A) (p : A) :
    shift (orbitEmbedding f p) = orbitEmbedding f (f p) := by
  funext i
  change ((f ^ (i + 1)) p).val = ((f ^ i) (f p)).val
  rw [zpow_add, zpow_one, Homeomorph.mul_apply]

theorem orbitEmbedding_range_closed {A : Set CantorSpace} (hA : IsClosed A)
    (f : A ≃ₜ A) : IsClosed (Set.range (orbitEmbedding f)) := by
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  exact (isCompact_range (continuous_orbitEmbedding f)).isClosed

theorem orbitEmbedding_range_nowhereDense {A : Set CantorSpace}
    (hA : IsClosed A) (hnA : IsNowhereDense A) (f : A ≃ₜ A) :
    IsNowhereDense (Set.range (orbitEmbedding f)) := by
  have hd := (isClosed_isNowhereDense_iff_compl.mp ⟨hA, hnA⟩).2
  have hp : IsNowhereDense ((fun x : ShiftSpace => x 0) ⁻¹' A) := by
    have hdpre : Dense ((fun x : ShiftSpace => x 0) ⁻¹' Aᶜ) :=
      hd.preimage (isOpenMap_eval (X := fun _ : ℤ => CantorSpace) 0)
    exact (isClosed_isNowhereDense_iff_compl.mpr
      (show IsOpen (((fun x : ShiftSpace => x 0) ⁻¹' A)ᶜ) ∧
          Dense (((fun x : ShiftSpace => x 0) ⁻¹' A)ᶜ) from
        ⟨(hA.preimage (continuous_apply 0)).isOpen_compl, hdpre⟩)).2
  apply hp.mono
  rintro _ ⟨p, rfl⟩
  simp [orbitEmbedding]

/-- Coordinate reshuffling, preserving the product topologies. -/
noncomputable def flatten : CantorSpace ≃ₜ ShiftSpace :=
  cantorSpaceHomeomorphNatToCantorSpace.trans
    (Homeomorph.piCongrLeft (Y := fun _ : ℤ => CantorSpace) (Denumerable.eqv ℤ).symm)

noncomputable def encodedOrbit {A : Set CantorSpace} (f : A ≃ₜ A) (p : A) : CantorSpace :=
  flatten.symm (orbitEmbedding f p)

theorem continuous_encodedOrbit {A : Set CantorSpace} (f : A ≃ₜ A) :
    Continuous (encodedOrbit f) :=
  flatten.symm.continuous.comp (continuous_orbitEmbedding f)

theorem encodedOrbit_injective {A : Set CantorSpace} (f : A ≃ₜ A) :
    Function.Injective (encodedOrbit f) :=
  flatten.symm.injective.comp (orbitEmbedding_injective f)

theorem encodedOrbit_range_nowhereDense {A : Set CantorSpace}
    (hA : IsClosed A) (hnA : IsNowhereDense A) (f : A ≃ₜ A) :
    IsNowhereDense (Set.range (encodedOrbit f)) := by
  have h := flatten.symm.isEmbedding.isInducing.isNowhereDense_image
    (orbitEmbedding_range_nowhereDense hA hnA f)
  change IsNowhereDense (Set.range (flatten.symm ∘ orbitEmbedding f))
  rw [Set.range_comp]
  exact h

/-- Extend the orbit embedding to the ambient Cantor space. This constructs a
conjugating homeomorphism, without assuming an ambient extension exists. -/
theorem exists_ambient_orbitEmbedding {A : Set CantorSpace}
    (hA : IsClosed A) (hnA : IsNowhereDense A) (f : A ≃ₜ A) :
    ∃ E : CantorSpace ≃ₜ ShiftSpace, ∀ p : A, E p.val = orbitEmbedding f p := by
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  have he := (continuous_encodedOrbit f).isClosedEmbedding (encodedOrbit_injective f)
  obtain ⟨E, hE⟩ := KnasterReichbach.exists_homeomorph_extension hA hnA
    he.isClosed_range (encodedOrbit_range_nowhereDense hA hnA f) he.isEmbedding.toHomeomorph
  refine ⟨E.trans flatten, fun p => ?_⟩
  change flatten (E p.val) = orbitEmbedding f p
  rw [hE]
  exact flatten.apply_symm_apply _

end CantorDynamics
