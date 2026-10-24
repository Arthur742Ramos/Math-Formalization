module
public import WeakMixingCore
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic

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
