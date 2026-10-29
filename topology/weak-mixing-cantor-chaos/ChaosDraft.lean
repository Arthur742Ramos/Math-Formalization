/-
Development draft: weak mixing and Cantor families of dense square orbits.
Countable-basis construction adapts IPTransitive.residual_dense_orbits,
topology/ip-transitive-points/IPTransitive.lean at a6fd933f00c83a82c4d7ab510d17ae62e87dc75f
(blob 40afb48ddf57a1f7a35e2706d346ae6baaed9a54). Cantor fusion is
Mycielski.exists_cantor_independent from the same tree, blob
c0c0615effc8abd76b78470a6e61261d0aad8b94. Both are Apache-2.0.
-/
import Mycielski.Independent
import Mathlib.Tactic

open Set Function TopologicalSpace

namespace CantorChaos

/-- Open-set transitivity includes time zero. -/
def OpenTransitive {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ n : ℕ, ∃ z ∈ U, f^[n] z ∈ V

def pairMap {X : Type*} (f : X → X) (p : X × X) : X × X := (f p.1, f p.2)

def DenseOrbit {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  Dense (range (fun n : ℕ => f^[n] x))

/-- A local Cantor family whose distinct ordered pairs have dense square orbit. -/
theorem cantor_dense_pair_orbits {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [PerfectSpace X] (f : X → X) (hf : Continuous f)
    (ht : OpenTransitive (pairMap f)) {U : Set X} (hU : IsOpen U)
    (hneU : U.Nonempty) :
    ∃ e : Mycielski.CantorSpace → X, Topology.IsClosedEmbedding e ∧ range e ⊆ U ∧
      ∀ s t, s ≠ t → DenseOrbit (pairMap f) (e s, e t) := by
  classical
  have hf2 : Continuous (pairMap f) :=
    (hf.comp continuous_fst).prodMk (hf.comp continuous_snd)
  obtain ⟨B, hB⟩ := exists_seq_basis (X × X)
  let R : ℕ → Set (X × X) := fun i =>
    if (B i).Nonempty then {z | ∃ n : ℕ, (pairMap f)^[n] z ∈ B i} else univ
  have hRo : ∀ i, IsOpen (R i) := by
    intro i
    have hBi : IsOpen (B i) := hB.isOpen ⟨i, rfl⟩
    by_cases hne : (B i).Nonempty
    · simp only [R, ite_eq_left hne]
      rw [show {z | ∃ n : ℕ, (pairMap f)^[n] z ∈ B i} =
          (⋃ n : ℕ, (pairMap f)^[n] ⁻¹' B i) by ext z; simp]
      exact isOpen_iUnion fun n => hBi.preimage (hf2.iterate n)
    · simp [R, hne]
  have hRd : ∀ i, Dense (R i) := by
    intro i
    by_cases hne : (B i).Nonempty
    · simp only [R, ite_eq_left hne]
      apply dense_iff_inter_open.mpr
      intro V hV hnV
      obtain ⟨n, z, hz, htarget⟩ :=
        ht V (B i) hV hnV (hB.isOpen ⟨i, rfl⟩) hne
      exact ⟨z, hz, n, htarget⟩
    · simp [R, hne]
  obtain ⟨e, he, heU, hrel⟩ := Mycielski.exists_cantor_independent hU hneU R hRo hRd
  refine ⟨e, he, heU, ?_⟩
  intro s t hst
  apply hB.dense_iff.mpr
  intro V hVB hVne
  obtain ⟨i, rfl⟩ := hVB
  have hne : (B i).Nonempty := hVne
  have hhit := hrel s t hst i
  simp only [R, ite_eq_left hne, mem_ofPred_eq] at hhit
  obtain ⟨n, hn⟩ := hhit
  exact ⟨(pairMap f)^[n] (e s, e t), hn, n, rfl⟩

open Filter
open scoped Topology

/-- Coordinatewise iteration of the square action. Adapted from IPTransitive. -/
theorem iterate_pairMap {X : Type*} (f : X → X) (n : ℕ) (p : X × X) :
    (pairMap f)^[n] p = (f^[n] p.1, f^[n] p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply, ih, pairMap]

/-- A dense sequence in a T1 space without isolated points visits open sets
arbitrarily late. Adapted from IPTransitive.dense_hits_after. -/
theorem dense_hits_after {X : Type*} [TopologicalSpace X] [T1Space X]
    [∀ x : X, NeBot (𝓝[≠] x)] (g : ℕ → X) (hg : Dense (range g))
    (U : Set X) (hU : IsOpen U) (hu : U.Nonempty) (N : ℕ) :
    ∃ n, N ≤ n ∧ g n ∈ U := by
  classical
  let E : Set X := g '' Set.Iio N
  have hE : E.Finite := (Set.finite_Iio N).image g
  obtain ⟨z, hzU, hz⟩ := (hg.sdiff_finite hE).inter_open_nonempty U hU hu
  obtain ⟨⟨n, rfl⟩, hn⟩ := hz
  refine ⟨n, Nat.le_of_not_gt ?_, hzU⟩
  intro h
  exact hn ⟨n, h, rfl⟩

/-- A transitive square with an isolated point forces a trivial system.
Adapted from IPTransitive.subsingleton_of_open_singleton. -/
theorem subsingleton_of_open_singleton {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : X → X) (ht : OpenTransitive (pairMap f)) (a : X) (ha : IsOpen ({a} : Set X)) :
    Subsingleton X := by
  refine ⟨?_⟩
  intro x y
  by_contra hxy
  obtain ⟨U, V, hU, hV, hxU, hyV, hdis⟩ := t2_separation hxy
  obtain ⟨n, z, hz, htarget⟩ := ht (({a} : Set X) ×ˢ {a}) (U ×ˢ V)
    (ha.prod ha) (Set.singleton_nonempty a |>.prod (Set.singleton_nonempty a))
    (hU.prod hV) (Set.Nonempty.prod ⟨x, hxU⟩ ⟨y, hyV⟩)
  have hz' : z = (a, a) := by simpa only [mem_prod, mem_singleton_iff, Prod.ext_iff] using hz
  subst z
  rw [iterate_pairMap] at htarget
  exact (Set.disjoint_left.mp hdis) htarget.1 htarget.2

/-- The square of a nontrivial weakly mixing Hausdorff system has no isolated
points. Adapted from IPTransitive.square_punctured_neBot. -/
theorem square_punctured_neBot {X : Type*} [TopologicalSpace X] [T2Space X] [Nontrivial X]
    (f : X → X) (ht : OpenTransitive (pairMap f)) (z : X × X) :
    NeBot (𝓝[≠] z) := by
  refine ⟨?_⟩
  intro hbot
  have hz : IsOpen ({z} : Set (X × X)) := (isOpen_singleton_iff_punctured_nhds z).2 hbot
  have ha : IsOpen ({z.1} : Set X) := by
    have hpre := hz.preimage (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => z.2)))
    convert hpre using 1
    ext w
    cases z with
    | mk a b => simp
  have hsub := subsingleton_of_open_singleton f ht z.1 ha
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  exact hab (hsub.elim a b)

/-- A common separation scale works for every pair in each locally constructed
Cantor family; both closeness and separation occur arbitrarily late. -/
theorem cantor_uniform_scrambled {X : Type*} [MetricSpace X] [PolishSpace X]
    [PerfectSpace X] [Nontrivial X] (f : X → X) (hf : Continuous f)
    (ht : OpenTransitive (pairMap f)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ e : Mycielski.CantorSpace → X, Topology.IsClosedEmbedding e ∧ range e ⊆ U ∧
        ∀ s t, s ≠ t →
          (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, dist (f^[n] (e s)) (f^[n] (e t)) < ε) ∧
          (∀ N : ℕ, ∃ n ≥ N, δ < dist (f^[n] (e s)) (f^[n] (e t))) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have hd : 0 < dist a b := dist_pos.mpr hab
  let δ : ℝ := dist a b / 2
  refine ⟨δ, by dsimp [δ]; linarith, ?_⟩
  intro U hU hneU
  obtain ⟨e, he, heU, hpair⟩ := cantor_dense_pair_orbits f hf ht hU hneU
  refine ⟨e, he, heU, ?_⟩
  intro s t hst
  let (z : X × X) : NeBot (𝓝[≠] z) := square_punctured_neBot f ht z
  constructor
  · intro ε hε N
    let V : Set (X × X) := {z | dist z.1 z.2 < ε}
    have hV : IsOpen V := isOpen_lt (continuous_fst.dist continuous_snd) continuous_const
    have hVne : V.Nonempty := ⟨(a, a), by simpa [V] using hε⟩
    obtain ⟨n, hn, hhit⟩ := dense_hits_after
      (fun n => (pairMap f)^[n] (e s, e t)) (hpair s t hst) V hV hVne N
    refine ⟨n, hn, ?_⟩
    simpa [V, iterate_pairMap] using hhit
  · intro N
    let V : Set (X × X) := {z | δ < dist z.1 z.2}
    have hV : IsOpen V := isOpen_lt continuous_const (continuous_fst.dist continuous_snd)
    have hVne : V.Nonempty := ⟨(a, b), by dsimp [V, δ]; linarith⟩
    obtain ⟨n, hn, hhit⟩ := dense_hits_after
      (fun n => (pairMap f)^[n] (e s, e t)) (hpair s t hst) V hV hVne N
    refine ⟨n, hn, ?_⟩
    simpa [V, iterate_pairMap] using hhit

end CantorChaos
