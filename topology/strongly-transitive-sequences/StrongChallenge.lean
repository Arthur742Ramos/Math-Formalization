module
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Polish

/-! Finite common-hit infrastructure copied with attribution from campaign source9e5b57dba2ba9423cc8f12ff934bd07d86394c47, topology/furstenberg-weak-mixing/WeakMixingPower.lean. New countable-product and category arguments are in StrongTransitive.lean. -/

@[expose] public section
open Set Function
namespace Furstenberg

/-- Natural forward hitting times, including zero. -/
abbrev Hit {X : Type*} (f : X → X) (U V : Set X) (n : ℕ) : Prop :=
  ∃ x, x ∈ U ∧ f^[n] x ∈ V

/-- Open-set transitivity, with no dense-orbit assertion. -/
abbrev Transitive {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty → ∃ n, Hit f U V n

/-- The literal two-pair hitting-time condition, related to the square below. -/
abbrev WeakMixing {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ U₁ V₁ U₂ V₂ : Set X, IsOpen U₁ → U₁.Nonempty → IsOpen V₁ → V₁.Nonempty →
    IsOpen U₂ → U₂.Nonempty → IsOpen V₂ → V₂.Nonempty →
    ∃ n, Hit f U₁ V₁ n ∧ Hit f U₂ V₂ n

def pairMap {X : Type*} (f : X → X) (p : X × X) : X × X := (f p.1, f p.2)
def diagonal {X : Type*} (f : X → X) (ι : Type*) (x : ι → X) : ι → X := fun i => f (x i)

theorem iterate_pairMap {X : Type*} (f : X → X) (n : ℕ) (p : X × X) :
    (pairMap f)^[n] p = (f^[n] p.1, f^[n] p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply, ih, pairMap]

theorem iterate_diagonal {X ι : Type*} (f : X → X) (n : ℕ) (x : ι → X) (i : ι) :
    (diagonal f ι)^[n] x i = f^[n] (x i) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply, ih, diagonal]

/-- Weak mixing is actual transitivity of the square with its product topology. -/
theorem weakMixing_iff_product_transitive {X : Type*} [TopologicalSpace X] (f : X → X) :
    WeakMixing f ↔ Transitive (pairMap f) := by
  constructor
  · intro hw U V hU hnU hV hnV
    obtain ⟨x, hx⟩ := hnU
    obtain ⟨y, hy⟩ := hnV
    obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := isOpen_prod_iff.mp hU x.1 x.2 hx
    obtain ⟨C, D, hC, hD, hyC, hyD, hCD⟩ := isOpen_prod_iff.mp hV y.1 y.2 hy
    obtain ⟨n, ⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ :=
      hw A C B D hA ⟨x.1, hxA⟩ hC ⟨y.1, hyC⟩ hB ⟨x.2, hxB⟩ hD ⟨y.2, hyD⟩
    refine ⟨n, (a, b), hAB ⟨ha, hb⟩, ?_⟩
    rw [iterate_pairMap]
    exact hCD ⟨hfa, hfb⟩
  · intro ht U₁ V₁ U₂ V₂ hU₁ hnU₁ hV₁ hnV₁ hU₂ hnU₂ hV₂ hnV₂
    obtain ⟨n, x, hx, hfx⟩ := ht (U₁ ×ˢ U₂) (V₁ ×ˢ V₂)
      (hU₁.prod hU₂) (hnU₁.prod hnU₂) (hV₁.prod hV₂) (hnV₁.prod hnV₂)
    rw [iterate_pairMap] at hfx
    exact ⟨n, ⟨x.1, hx.1, hfx.1⟩, ⟨x.2, hx.2, hfx.2⟩⟩

/-- Furstenberg's refinement puts a hitting-time set inside two prescribed ones. -/
theorem hitting_refinement {X : Type*} [TopologicalSpace X] (f : X → X)
    (hf : Continuous f) (hw : WeakMixing f) (U₁ V₁ U₂ V₂ : Set X)
    (hU₁ : IsOpen U₁) (hnU₁ : U₁.Nonempty) (hV₁ : IsOpen V₁) (hnV₁ : V₁.Nonempty)
    (hU₂ : IsOpen U₂) (hnU₂ : U₂.Nonempty) (hV₂ : IsOpen V₂) (hnV₂ : V₂.Nonempty) :
    ∃ W Z : Set X, IsOpen W ∧ W.Nonempty ∧ IsOpen Z ∧ Z.Nonempty ∧
      ∀ n, Hit f W Z n → Hit f U₁ V₁ n ∧ Hit f U₂ V₂ n := by
  obtain ⟨k, hkU, hkV⟩ := hw U₁ U₂ V₁ V₂ hU₁ hnU₁ hU₂ hnU₂ hV₁ hnV₁ hV₂ hnV₂
  refine ⟨U₁ ∩ f^[k] ⁻¹' U₂, V₁ ∩ f^[k] ⁻¹' V₂,
    hU₁.inter (hU₂.preimage (hf.iterate k)), hkU,
    hV₁.inter (hV₂.preimage (hf.iterate k)), hkV, ?_⟩
  rintro n ⟨x, hx, hfx⟩
  refine ⟨⟨x, hx.1, hfx.1⟩, f^[k] x, hx.2, ?_⟩
  rw [← iterate_add_apply, Nat.add_comm, iterate_add_apply]
  exact hfx.2

/-- The induction retains a nonempty open pair refining every accumulated constraint. -/
theorem finite_refinement {X ι : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hw : WeakMixing f) (s : Finset ι)
    (U V : ι → Set X) (hU : ∀ i ∈ s, IsOpen (U i) ∧ (U i).Nonempty)
    (hV : ∀ i ∈ s, IsOpen (V i) ∧ (V i).Nonempty) :
    ∃ W Z : Set X, IsOpen W ∧ W.Nonempty ∧ IsOpen Z ∧ Z.Nonempty ∧
      ∀ n, Hit f W Z n → ∀ i ∈ s, Hit f (U i) (V i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨univ, univ, isOpen_univ, Set.univ_nonempty, isOpen_univ,
      Set.univ_nonempty, fun _ _ i hi => False.elim (Finset.notMem_empty i hi)⟩
  | @insert i s hi ih =>
    obtain ⟨W, Z, hW, hnW, hZ, hnZ, href⟩ := ih
      (fun j hj => hU j (Finset.mem_insert_of_mem hj))
      (fun j hj => hV j (Finset.mem_insert_of_mem hj))
    obtain ⟨A, B, hA, hnA, hB, hnB, hAB⟩ := hitting_refinement f hf hw W Z (U i) (V i)
      hW hnW hZ hnZ (hU i (Finset.mem_insert_self i s)).1
      (hU i (Finset.mem_insert_self i s)).2 (hV i (Finset.mem_insert_self i s)).1
      (hV i (Finset.mem_insert_self i s)).2
    refine ⟨A, B, hA, hnA, hB, hnB, ?_⟩
    intro n hn j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hAB n hn).2
    · exact href n (hAB n hn).1 j hj

/-- Every finite family of nonempty open pairs has a common natural hitting time. -/
theorem finite_simultaneous_hitting {X ι : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hw : WeakMixing f) (s : Finset ι)
    (U V : ι → Set X) (hU : ∀ i ∈ s, IsOpen (U i) ∧ (U i).Nonempty)
    (hV : ∀ i ∈ s, IsOpen (V i) ∧ (V i).Nonempty) :
    ∃ n, ∀ i ∈ s, Hit f (U i) (V i) n := by
  obtain ⟨W, Z, hW, hnW, hZ, hnZ, href⟩ := finite_refinement f hf hw s U V hU hV
  obtain ⟨n, hn, _⟩ := hw W Z W Z hW hnW hZ hnZ hW hnW hZ hnZ
  exact ⟨n, href n hn⟩

/-- Every finite diagonal power is transitive for its actual product topology, even power zero. -/
theorem finite_power_transitive {X : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hw : WeakMixing f) (k : ℕ) :
    Transitive (diagonal f (Fin k)) := by
  classical
  intro U V hU hnU hV hnV
  obtain ⟨x, hx⟩ := hnU
  obtain ⟨y, hy⟩ := hnV
  obtain ⟨A, hA, hAU⟩ := isOpen_pi_iff'.mp hU x hx
  obtain ⟨B, hB, hBV⟩ := isOpen_pi_iff'.mp hV y hy
  obtain ⟨n, hn⟩ := finite_simultaneous_hitting f hf hw Finset.univ A B
    (fun i _ => ⟨(hA i).1, x i, (hA i).2⟩)
    (fun i _ => ⟨(hB i).1, y i, (hB i).2⟩)
  choose z hzA hzB using fun i => hn i (Finset.mem_univ i)
  refine ⟨n, z, hAU (fun i _ => hzA i), hBV ?_⟩
  intro i _
  rw [iterate_diagonal]
  exact hzB i

end Furstenberg

@[expose] public section
open Set Filter Function TopologicalSpace
open scoped Topology
namespace StrongTransitive

/-- Density of the actual natural forward orbit, including time zero. -/
abbrev DenseOrbit {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  Dense (range (fun n : ℕ => f^[n] x))

/-- The coherent initial k coordinates, in their actual finite product topology. -/
def initialSegment {X : Type*} (k : ℕ) (x : ℕ → X) : Fin k → X := fun i => x i.val

/-- Every finite prefix has a dense diagonal orbit at shared natural times. -/
abbrev StrongSequence {X : Type*} [TopologicalSpace X] (f : X → X) (x : ℕ → X) : Prop :=
  ∀ k : ℕ, DenseOrbit (Furstenberg.diagonal f (Fin k)) (initialSegment k x)

/-- The countable-basis category construction. Baire is not needed for residual membership. -/
theorem residual_dense_orbits {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (f : X → X) (hf : Continuous f) (ht : Furstenberg.Transitive f) :
    {x : X | DenseOrbit f x} ∈ residual X := by
  classical
  obtain ⟨B, hBc, hB0, hB⟩ := exists_countable_basis X
  have : Countable B := hBc
  have hhit (U : B) : {x : X | ∃ n : ℕ, f^[n] x ∈ U.val} ∈ residual X := by
    have hnU : U.val.Nonempty := nonempty_iff_ne_empty.mpr (fun h => hB0 (h ▸ U.property))
    have hopen : IsOpen {x : X | ∃ n : ℕ, f^[n] x ∈ U.val} := by
      rw [show {x : X | ∃ n : ℕ, f^[n] x ∈ U.val} = (⋃ n : ℕ, f^[n] ⁻¹' U.val) by
        ext x; simp]
      exact isOpen_iUnion fun n => (hB.isOpen U.property).preimage (hf.iterate n)
    apply residual_of_dense_open hopen
    apply dense_iff_inter_open.mpr
    intro V hV hnV
    obtain ⟨n, x, hxV, hxU⟩ := ht V U.val hV hnV (hB.isOpen U.property) hnU
    exact ⟨x, hxV, n, hxU⟩
  have hall : {x : X | ∀ U : B, ∃ n : ℕ, f^[n] x ∈ U.val} ∈ residual X :=
    eventually_countable_forall.mpr hhit
  refine mem_of_superset hall ?_
  intro x hx
  apply hB.dense_iff.mpr
  intro U hUB _
  obtain ⟨n, hn⟩ := hx ⟨U, hUB⟩
  exact ⟨f^[n] x, hn, n, rfl⟩

/-- Finite cylinders combine at one shared time, so the actual countable power is transitive. -/
theorem countable_power_transitive {X : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hw : Furstenberg.WeakMixing f) :
    Furstenberg.Transitive (Furstenberg.diagonal f ℕ) := by
  classical
  intro U V hU hnU hV hnV
  obtain ⟨x, hx⟩ := hnU
  obtain ⟨y, hy⟩ := hnV
  obtain ⟨S, A, hA, hAU⟩ := isOpen_pi_iff.mp hU x hx
  obtain ⟨T, B, hB, hBV⟩ := isOpen_pi_iff.mp hV y hy
  let P : ℕ → Set X := fun i => if i ∈ S then A i else univ
  let Q : ℕ → Set X := fun i => if i ∈ T then B i else univ
  have hP (i : ℕ) (_hi : i ∈ S ∪ T) : IsOpen (P i) ∧ (P i).Nonempty := by
    by_cases hi : i ∈ S
    · simpa [P, hi] using ⟨(hA i hi).1, x i, (hA i hi).2⟩
    · simp [P, hi]
  have hQ (i : ℕ) (_hi : i ∈ S ∪ T) : IsOpen (Q i) ∧ (Q i).Nonempty := by
    by_cases hi : i ∈ T
    · simpa [Q, hi] using ⟨(hB i hi).1, y i, (hB i hi).2⟩
    · simp [Q, hi]
  obtain ⟨n, hn⟩ := Furstenberg.finite_simultaneous_hitting f hf hw (S ∪ T) P Q hP hQ
  choose z hzP hzQ using fun i : {i // i ∈ S ∪ T} => hn i.val i.property
  let w : ℕ → X := fun i => if hi : i ∈ S ∪ T then z ⟨i, hi⟩ else x i
  refine ⟨n, w, hAU ?_, hBV ?_⟩
  · intro i hi
    have hiS : i ∈ S := hi
    have hu : i ∈ S ∪ T := Finset.mem_union_left T hiS
    rw [show w i = z ⟨i, hu⟩ from dite_eq_left hu]
    simpa only [P, ite_eq_left hiS] using hzP ⟨i, hu⟩
  · intro i hi
    have hiT : i ∈ T := hi
    have hu : i ∈ S ∪ T := Finset.mem_union_right S hiT
    rw [Furstenberg.iterate_diagonal]
    rw [show w i = z ⟨i, hu⟩ from dite_eq_left hu]
    simpa only [Q, ite_eq_left hiT] using hzQ ⟨i, hu⟩

/-- Projection of one countable-product orbit supplies coherent dense finite-prefix orbits. -/
theorem dense_prefix_orbit {X : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) {x : ℕ → X} (hx : DenseOrbit (Furstenberg.diagonal f ℕ) x) (k : ℕ) :
    DenseOrbit (Furstenberg.diagonal f (Fin k)) (initialSegment k x) := by
  classical
  have hp : Surjective (initialSegment (X := X) k) := by
    intro y
    refine ⟨fun n => if h : n < k then y ⟨n, h⟩ else Classical.choice ‹Nonempty X›, ?_⟩
    funext i
    simp [initialSegment, i.isLt]
  have hc : Continuous (initialSegment (X := X) k) := continuous_pi fun i => continuous_apply i.val
  have hd := hp.denseRange.comp hx hc
  change Dense (range (fun n : ℕ => initialSegment k ((Furstenberg.diagonal f ℕ)^[n] x))) at hd
  have he : (fun n : ℕ => initialSegment k ((Furstenberg.diagonal f ℕ)^[n] x)) =
      fun n => (Furstenberg.diagonal f (Fin k))^[n] (initialSegment k x) := by
    funext n i
    simp only [initialSegment, Furstenberg.iterate_diagonal]
  rw [he] at hd
  exact hd

/-- Generic coherent strongly transitive sequences in a nonempty Polish weakly mixing system. -/
theorem residual_strong_sequences {X : Type*} [TopologicalSpace X] [PolishSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hw : Furstenberg.WeakMixing f) :
    {x : ℕ → X | StrongSequence f x} ∈ residual (ℕ → X) := by
  have hc : Continuous (Furstenberg.diagonal f ℕ) :=
    continuous_pi fun i => hf.comp (continuous_apply i)
  refine mem_of_superset (residual_dense_orbits _ hc (countable_power_transitive f hf hw)) ?_
  intro x hx k
  exact dense_prefix_orbit f hx k

/-- Baire category turns residual membership into an actual nonempty dense G-delta family. -/
theorem exists_dense_Gdelta_strong_sequences {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [Nonempty X] (f : X → X) (hf : Continuous f) (hw : Furstenberg.WeakMixing f) :
    ∃ C : Set (ℕ → X), IsGδ C ∧ Dense C ∧ C.Nonempty ∧ ∀ x ∈ C, StrongSequence f x := by
  obtain ⟨C, hC, hG, hd⟩ := mem_residual.mp (residual_strong_sequences f hf hw)
  exact ⟨C, hG, hd, hd.nonempty, hC⟩

end StrongTransitive
