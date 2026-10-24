module
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Logic.Function.Conjugate

/-! Finite common-hit infrastructure copied with attribution from campaign source9e5b57dba2ba9423cc8f12ff934bd07d86394c47, topology/furstenberg-weak-mixing/WeakMixingPower.lean. New factor-transfer and metric equicontinuity-obstruction arguments are in WeakMixingFactors.lean. -/

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
open Set Function Metric
namespace MixingFactor

/-- Equicontinuity at one point of the actual forward iterate family, including time zero. -/
def OrbitEquicontinuousAt {X : Type*} [MetricSpace X] (f : X → X) (x : X) : Prop :=
  EquicontinuousAt (fun n : ℕ => f^[n]) x

/-- Weak mixing is inherited by continuous surjective semiconjugate factors. -/
theorem weakMixing_factor {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (g : Y → Y) (π : X → Y) (hπ : Continuous π)
    (hs : Surjective π) (hc : Semiconj π f g) (hw : Furstenberg.WeakMixing f) :
    Furstenberg.WeakMixing g := by
  intro U V A B hU hnU hV hnV hA hnA hB hnB
  obtain ⟨n, ⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hw
    (π ⁻¹' U) (π ⁻¹' V) (π ⁻¹' A) (π ⁻¹' B)
    (hU.preimage hπ) (hnU.preimage hs) (hV.preimage hπ) (hnV.preimage hs)
    (hA.preimage hπ) (hnA.preimage hs) (hB.preimage hπ) (hnB.preimage hs)
  refine ⟨n, ⟨π x, hx, ?_⟩, ⟨π y, hy, ?_⟩⟩
  · simpa only [mem_preimage, hc.iterate_right n x] using hfx
  · simpa only [mem_preimage, hc.iterate_right n y] using hfy

/-- A single equicontinuity point is incompatible with nontrivial metric weak mixing. -/
theorem subsingleton_of_equicontinuousAt {X : Type*} [MetricSpace X]
    (f : X → X) (hw : Furstenberg.WeakMixing f) (x : X)
    (he : OrbitEquicontinuousAt f x) : Subsingleton X := by
  constructor
  intro a b
  by_contra hab
  have hd : 0 < dist a b := dist_pos.mpr hab
  let ε := dist a b / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.equicontinuousAt_iff.mp he ε hε
  obtain ⟨n, ⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩ := hw
    (ball x δ) (ball a ε) (ball x δ) (ball b ε)
    isOpen_ball (nonempty_ball.mpr hδ) isOpen_ball (nonempty_ball.mpr hε)
    isOpen_ball (nonempty_ball.mpr hδ) isOpen_ball (nonempty_ball.mpr hε)
  have hcu : dist (f^[n] u) (f^[n] x) < ε := by
    simpa only [dist_comm] using hclose u hu n
  have hcv : dist (f^[n] x) (f^[n] v) < ε := hclose v hv n
  have hua : dist a (f^[n] u) < ε := by simpa only [mem_ball, dist_comm] using hfu
  have hvb : dist (f^[n] v) b < ε := hfv
  have h1 := dist_triangle a (f^[n] u) b
  have h2 := dist_triangle (f^[n] u) (f^[n] x) b
  have h3 := dist_triangle (f^[n] x) (f^[n] v) b
  dsimp [ε] at *
  linarith

/-- Every equicontinuous metric factor of a weakly mixing topological map is subsingleton. -/
theorem equicontinuous_factor_subsingleton {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y] (f : X → X) (g : Y → Y) (π : X → Y)
    (hπ : Continuous π) (hs : Surjective π) (hc : Semiconj π f g)
    (hw : Furstenberg.WeakMixing f) (he : Equicontinuous (fun n : ℕ => g^[n])) :
    Subsingleton Y := by
  have hgw := weakMixing_factor f g π hπ hs hc hw
  constructor
  intro a b
  have hsub := subsingleton_of_equicontinuousAt g hgw a (he a)
  exact @Subsingleton.elim Y hsub a b

end MixingFactor
