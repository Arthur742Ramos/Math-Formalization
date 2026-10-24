module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Tactic


@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology
namespace EZero

/-- The actual binary product, with its inferred product topology. -/
abbrev CantorSpace := ℕ → Bool
/-- Eventual equality of values, not a permutation of coordinates. -/
abbrev E0 (x y : CantorSpace) : Prop := ∃ N : ℕ, ∀ n, N ≤ n → x n = y n
/-- Every open inverse image has the property of Baire. -/
abbrev BPPreimages {Y : Type*} [TopologicalSpace Y] (f : CantorSpace → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- Coordinatewise xor by a fixed binary mask is an involutive homeomorphism. -/
def maskHomeomorph (m : ℕ → Bool) : CantorSpace ≃ₜ CantorSpace where
  toFun x n := Bool.xor (m n) (x n)
  invFun x n := Bool.xor (m n) (x n)
  left_inv x := by
    funext n
    change Bool.xor (m n) (Bool.xor (m n) (x n)) = x n
    cases m n <;> cases x n <;> rfl
  right_inv x := by
    funext n
    change Bool.xor (m n) (Bool.xor (m n) (x n)) = x n
    cases m n <;> cases x n <;> rfl
  continuous_toFun := continuous_pi fun n =>
    (continuous_of_discreteTopology : Continuous (Bool.xor (m n))).comp (continuous_apply n)
  continuous_invFun := continuous_pi fun n =>
    (continuous_of_discreteTopology : Continuous (Bool.xor (m n))).comp (continuous_apply n)

@[simp] theorem maskHomeomorph_apply (m : ℕ → Bool) (x : CantorSpace) (n : ℕ) :
    maskHomeomorph m x n = Bool.xor (m n) (x n) := rfl

/-- Flip exactly the finite set of indicated coordinates. -/
def flip (s : Finset ℕ) : CantorSpace ≃ₜ CantorSpace :=
  maskHomeomorph (fun n => decide (n ∈ s))

theorem e0_flip (s : Finset ℕ) (x : CantorSpace) : E0 x (flip s x) := by
  refine ⟨s.sup id + 1, ?_⟩
  intro n hn
  have hs : n ∉ s := by
    intro h
    have hm := Finset.le_sup (f := id) h
    simp only [id_eq] at hm
    omega
  simp [flip, hs]

end EZero

@[expose] public section
open Set Filter
open scoped Topology
namespace EZero

/-- Adapted from the credited campaign category helper. The open approximation has a nonempty region when the Baire set is nonmeagre. -/
theorem open_residual_witness {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∃ S : Set X, S ∈ residual X ∧ U ∩ S ⊆ A := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hUne : U.Nonempty := by
    by_contra he
    apply hn
    change ∀ᶠ x in residual X, x ∉ A
    filter_upwards [hAU.mem_iff] with x hx
    exact fun hxa => he ⟨x, hx.mp hxa⟩
  refine ⟨U, hU, hUne, {x | x ∈ A ↔ x ∈ U}, hAU.mem_iff, ?_⟩
  exact fun x hx => hx.2.mpr hx.1

/-- An internal category zero-one argument. The product theorem proves, rather than
assumes, the required mixing condition for its coordinate homeomorphisms. -/
theorem zero_one_of_mixing {X I : Type*} [TopologicalSpace X] [BaireSpace X]
    (h : I → X ≃ₜ X)
    (hmix : ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ i, (U ∩ h i ⁻¹' V).Nonempty)
    {A : Set X} (hA : BaireMeasurableSet A)
    (hinv : ∀ i x, x ∈ A ↔ h i x ∈ A) : IsMeagre A ∨ IsMeagre Aᶜ := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨U, hU, hUne, S, hS, hSA⟩ := open_residual_witness hA hn.1
  obtain ⟨V, hV, hVne, T, hT, hTA⟩ := open_residual_witness hA.compl hn.2
  obtain ⟨i, hi⟩ := hmix U V hU hUne hV hVne
  have hpre : h i ⁻¹' T ∈ residual X :=
    (tendsto_residual_of_isOpenMap (h i).continuous (h i).isOpenMap) hT
  obtain ⟨x, ⟨hxU, hxV⟩, hxS, hxT⟩ :=
    (dense_of_mem_residual (inter_mem hS hpre)).inter_open_nonempty
      (U ∩ h i ⁻¹' V) (hU.inter (hV.preimage (h i).continuous)) hi
  exact hTA ⟨hxV, hxT⟩ ((hinv i x).mp (hSA ⟨hxU, hxS⟩))

end EZero

@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology
namespace EZero

/-- Finite changes of binary values connect any two nonempty open cylinders.
No orbit-density or mixing premise is supplied. -/
theorem finite_flip_mixing (U V : Set CantorSpace) (_hU : IsOpen U) (hneU : U.Nonempty)
    (hV : IsOpen V) (hneV : V.Nonempty) :
    ∃ s : Finset ℕ, (U ∩ flip s ⁻¹' V).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hneU
  obtain ⟨y, hy⟩ := hneV
  obtain ⟨S, v, hv, hsub⟩ := isOpen_pi_iff.mp hV y hy
  let s := S.filter (fun n => x n ≠ y n)
  have hm (n : ℕ) (hn : n ∈ S) : flip s x n = y n := by
    cases hx' : x n <;> cases hy' : y n <;> simp [flip, s, hn, hx', hy']
  refine ⟨s, x, hx, hsub ?_⟩
  intro n hn
  rw [hm n hn]
  exact (hv n hn).2

/-- E₀'s category zero-one law for its actual finite-value-change relation. -/
theorem zero_one {A : Set CantorSpace} (hA : BaireMeasurableSet A)
    (hinv : ∀ x y, E0 x y → (x ∈ A ↔ y ∈ A)) : IsMeagre A ∨ IsMeagre Aᶜ := by
  apply zero_one_of_mixing (fun s : Finset ℕ => flip s) finite_flip_mixing hA
  exact fun s x => hinv x (flip s x) (e0_flip s x)

end EZero

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