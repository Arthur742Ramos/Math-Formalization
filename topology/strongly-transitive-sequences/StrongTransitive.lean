module
public import WeakMixingCore
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Polish

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
