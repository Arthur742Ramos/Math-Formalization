module
public import EZero.Mixing

@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology
namespace EZero

/-- Every Baire-measurable E₀-invariant map into a second countable T0 space
has a comeagre constant fiber. No Polish or T2 target hypothesis is needed. -/
theorem generically_constant {Y : Type*} [TopologicalSpace Y]
    [SecondCountableTopology Y] [T0Space Y] (f : CantorSpace → Y) (hBP : BPPreimages f)
    (hinv : ∀ x y, E0 x y → f x = f y) :
    ∃ v : Y, {x : CantorSpace | f x = v} ∈ residual CantorSpace := by
  classical
  obtain ⟨B, hBc, _, hB⟩ := exists_countable_basis Y
  have : Countable B := hBc
  have hc (U : B) : ∃ P : Prop, {x : CantorSpace | x ∈ f ⁻¹' U.val ↔ P} ∈
      residual CantorSpace := by
    have hi : ∀ x y, E0 x y → (x ∈ f ⁻¹' U.val ↔ y ∈ f ⁻¹' U.val) := by
      intro x y hxy
      change f x ∈ U.val ↔ f y ∈ U.val
      rw [hinv x y hxy]
    rcases zero_one (hBP U.val (hB.isOpen U.property)) hi with hm | hm
    · refine ⟨False, ?_⟩
      change ∀ᶠ x in residual CantorSpace, x ∈ f ⁻¹' U.val ↔ False
      change ∀ᶠ x in residual CantorSpace, x ∉ f ⁻¹' U.val at hm
      simpa only [iff_false] using hm
    · refine ⟨True, ?_⟩
      change ∀ᶠ x in residual CantorSpace, x ∈ f ⁻¹' U.val ↔ True
      change ∀ᶠ x in residual CantorSpace, x ∉ (f ⁻¹' U.val)ᶜ at hm
      simpa only [mem_compl_iff, not_not, iff_true] using hm
  choose P hP using hc
  have hC : {x : CantorSpace | ∀ U : B, x ∈ f ⁻¹' U.val ↔ P U} ∈
      residual CantorSpace := eventually_countable_forall.mpr hP
  obtain ⟨x0, hx0⟩ := (dense_of_mem_residual hC).nonempty
  refine ⟨f x0, mem_of_superset hC ?_⟩
  intro x hx
  apply hB.eq_iff.mpr
  intro U hUB
  exact (hx ⟨U, hUB⟩).trans (hx0 ⟨U, hUB⟩).symm

/-- There is no Baire-measurable complete invariant for E₀ with values in a
second countable T0 space. The all-coordinate complement supplies the contradiction. -/
theorem no_baire_reduction {Y : Type*} [TopologicalSpace Y]
    [SecondCountableTopology Y] [T0Space Y] (f : CantorSpace → Y) (hBP : BPPreimages f) :
    ¬ (∀ x y : CantorSpace, E0 x y ↔ f x = f y) := by
  intro hr
  obtain ⟨v, hv⟩ := generically_constant f hBP (fun x y hxy => (hr x y).mp hxy)
  let J := maskHomeomorph (fun _ => true)
  have hpre : J ⁻¹' {x : CantorSpace | f x = v} ∈ residual CantorSpace :=
    (tendsto_residual_of_isOpenMap J.continuous J.isOpenMap) hv
  obtain ⟨x, hx, hJx⟩ := (dense_of_mem_residual (inter_mem hv hpre)).nonempty
  change f x = v at hx
  change f (J x) = v at hJx
  obtain ⟨N, hN⟩ := (hr x (J x)).mpr (hx.trans hJx.symm)
  have hbad := hN N (le_refl N)
  change x N = Bool.xor true (x N) at hbad
  cases hn : x N <;> simp [hn] at hbad

/-- Borel measurability refers explicitly to the Borel sigma-algebras of the
supplied topologies and implies the literal BP open-preimage hypothesis. -/
theorem bpPreimages_of_borel {Y : Type*} [TopologicalSpace Y] (f : CantorSpace → Y)
    (hf : @Measurable CantorSpace Y (borel CantorSpace) (borel Y) f) : BPPreimages f := by
  let : MeasurableSpace CantorSpace := borel CantorSpace
  have : BorelSpace CantorSpace := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  intro U hU
  exact (hf hU.measurableSet).baireMeasurableSet

/-- Standard non-smoothness: eventual equality has no Borel complete invariant
in any second countable T0 space, in particular in a Polish target. -/
theorem no_borel_reduction {Y : Type*} [TopologicalSpace Y]
    [SecondCountableTopology Y] [T0Space Y] (f : CantorSpace → Y)
    (hf : @Measurable CantorSpace Y (borel CantorSpace) (borel Y) f) :
    ¬ (∀ x y : CantorSpace, E0 x y ↔ f x = f y) :=
  no_baire_reduction f (bpPreimages_of_borel f hf)

end EZero
