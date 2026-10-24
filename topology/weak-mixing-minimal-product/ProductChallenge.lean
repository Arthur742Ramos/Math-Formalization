module
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Compact

/-! Finite common-hit infrastructure copied with attribution from campaign source9e5b57dba2ba9423cc8f12ff934bd07d86394c47, topology/furstenberg-weak-mixing/WeakMixingPower.lean. New surjectivity, thick/syndetic hitting and heterogeneous product arguments are in WeakMixingMinimal.lean. -/

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
open Set Function
namespace WeakMinimal

/-- Arbitrarily late inclusive blocks of every finite length. -/
def Thick (S : Set ℕ) : Prop := ∀ L N : ℕ, ∃ m, N ≤ m ∧ ∀ j ≤ L, m + j ∈ S
/-- A uniform inclusive bound on forward gaps, allowing bound zero. -/
def Syndetic (S : Set ℕ) : Prop := ∃ K : ℕ, ∀ k, ∃ j ≤ K, k + j ∈ S
/-- Pointwise minimality of the forward natural action. -/
def Minimal {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ x, Dense (range (fun n : ℕ => f^[n] x))
def productMap {X Y : Type*} (f : X → X) (g : Y → Y) (p : X × Y) : X × Y :=
  (f p.1, g p.2)

theorem iterate_productMap {X Y : Type*} (f : X → X) (g : Y → Y) (n : ℕ) (p : X × Y) :
    (productMap f g)^[n] p = (f^[n] p.1, g^[n] p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply, ih, productMap]

/-- Compactness closes the dense image forced by weak mixing, including isolated spaces. -/
theorem surjective_of_weakMixing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [Nonempty X] (f : X → X) (hf : Continuous f)
    (hw : Furstenberg.WeakMixing f) : Surjective f := by
  have hd : Dense (range f) := by
    rw [dense_iff_inter_open]
    intro U hU hnU
    obtain ⟨a⟩ := ‹Nonempty X›
    by_cases ha : f a ∈ U
    · exact ⟨f a, ha, a, rfl⟩
    obtain ⟨x, hx⟩ := hnU
    have hne : x ≠ f a := by rintro rfl; exact ha hx
    obtain ⟨A, B, hA, hB, hxA, haB, hd⟩ := t2_separation hne
    obtain ⟨n, ⟨z, _, hz⟩, ⟨w, hwA, hwB⟩⟩ :=
      hw univ U A B isOpen_univ univ_nonempty hU ⟨x, hx⟩ hA ⟨x, hxA⟩ hB ⟨f a, haB⟩
    cases n with
    | zero => exact False.elim (Set.disjoint_left.mp hd hwA hwB)
    | succ n => exact ⟨f (f^[n] z), by simpa only [iterate_succ_apply'] using hz, f^[n] z, rfl⟩
  have hc : IsClosed (range f) := hf.isClosedMap.isClosed_range
  intro y
  have hy : y ∈ range f := by rw [← hc.closure_eq]; exact hd y
  exact hy

/-- Finite simultaneous hitting yields arbitrarily late blocks, using proved surjectivity. -/
theorem hitting_thick {X : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hs : Surjective f) (hw : Furstenberg.WeakMixing f)
    (U V : Set X) (hU : IsOpen U) (hnU : U.Nonempty) (hV : IsOpen V)
    (hnV : V.Nonempty) : Thick {n | Furstenberg.Hit f U V n} := by
  intro L N
  obtain ⟨m, hm⟩ := Furstenberg.finite_simultaneous_hitting f hf hw
    (Finset.range (N + L + 1)) (fun _ => U) (fun j => f^[j] ⁻¹' V)
    (fun _ _ => ⟨hU, hnU⟩) (fun j _ =>
      ⟨hV.preimage (hf.iterate j), hnV.preimage (hs.iterate j)⟩)
  refine ⟨m + N, by omega, ?_⟩
  intro j hj
  obtain ⟨x, hx, hfx⟩ := hm (N + j) (Finset.mem_range.mpr (by omega))
  refine ⟨x, hx, ?_⟩
  simpa only [mem_preimage, ← iterate_add_apply, Nat.add_assoc, Nat.add_comm (N+j) m,
    ← Nat.add_assoc] using hfx

/-- Compactness turns pointwise orbit density into a uniform return-gap bound. -/
theorem minimal_hitting_syndetic {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (g : Y → Y) (hg : Continuous g) (hm : Minimal g) (U V : Set Y)
    (hnU : U.Nonempty) (hV : IsOpen V) (hnV : V.Nonempty) :
    Syndetic {n | Furstenberg.Hit g U V n} := by
  classical
  have hcover : (univ : Set Y) ⊆ ⋃ n : ℕ, g^[n] ⁻¹' V := by
    intro y _
    obtain ⟨z, hz, ⟨n, rfl⟩⟩ := (dense_iff_inter_open.mp (hm y)) V hV hnV
    exact mem_iUnion.mpr ⟨n, hz⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ => g^[n] ⁻¹' V) (fun n => hV.preimage (hg.iterate n)) hcover
  obtain ⟨y, hy⟩ := hnU
  refine ⟨s.sup id, ?_⟩
  intro k
  obtain ⟨j, hjs, hj⟩ := mem_iUnion₂.mp (hs (mem_univ (g^[k] y)))
  refine ⟨j, Finset.le_sup (f := id) hjs, y, hy, ?_⟩
  simpa only [mem_preimage, ← iterate_add_apply, Nat.add_comm j k] using hj

/-- An inclusive thick block meets a syndetic set, even with zero bound. -/
theorem thick_meets_syndetic (A B : Set ℕ) (ha : Thick A) (hb : Syndetic B) :
    (A ∩ B).Nonempty := by
  obtain ⟨K, hK⟩ := hb
  obtain ⟨m, _, hm⟩ := ha K 0
  obtain ⟨j, hj, hB⟩ := hK m
  exact ⟨m + j, hm j hj, hB⟩

/-- Furstenberg's product theorem for actual heterogeneous product dynamics. -/
theorem weakMixing_minimal_product {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [Nonempty X] [TopologicalSpace Y]
    [CompactSpace Y] [Nonempty Y] (f : X → X) (g : Y → Y)
    (hf : Continuous f) (hg : Continuous g) (hw : Furstenberg.WeakMixing f)
    (hm : Minimal g) : Furstenberg.Transitive (productMap f g) := by
  intro U V hU hnU hV hnV
  obtain ⟨x, hx⟩ := hnU
  obtain ⟨y, hy⟩ := hnV
  obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := isOpen_prod_iff.mp hU x.1 x.2 hx
  obtain ⟨C, D, hC, hD, hyC, hyD, hCD⟩ := isOpen_prod_iff.mp hV y.1 y.2 hy
  obtain ⟨n, ⟨a, ha, hfa⟩, ⟨b, hb, hgb⟩⟩ := thick_meets_syndetic _ _
    (hitting_thick f hf (surjective_of_weakMixing f hf hw) hw A C hA ⟨x.1,hxA⟩ hC ⟨y.1,hyC⟩)
    (minimal_hitting_syndetic g hg hm B D ⟨x.2,hxB⟩ hD ⟨y.2,hyD⟩)
  refine ⟨n, (a,b), hAB ⟨ha,hb⟩, ?_⟩
  rw [iterate_productMap]
  exact hCD ⟨hfa,hgb⟩

end WeakMinimal
