/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under the root Apache-2.0 license.
Material Lean proof authorship: OpenAI Codex.
Research source: Jian Li, Transitive points via Furstenberg family,
Topology and its Applications 158 (2011), Theorem 3.2.
Adapted repository proof fragments (Apache-2.0):
* Generic dense orbits: topology/strongly-transitive-sequences/StrongTransitive.lean
  at b507c8fd789af8ac5dee356ea2a85444209e401d (blob e47bf442d60d9fc11e4fa6e37c603d5ee4fc2b3a).
* Product section arguments: topology/kuratowski-ulam/KuratowskiUlam.lean
  at 0e3676798fe19b23d17defe9d732977d9f913f11 (blob a16038480bc2f517fcdcf77efe7c9bfd26a1e06d).
  Original file copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  and Ruy Jose Guerra Barretto de Queiroz; material Lean proof by OpenAI Codex.
* Pair iteration: topology/furstenberg-weak-mixing/WeakMixingPower.lean
  at 9e5b57dba2ba9423cc8f12ff934bd07d86394c47 (blob ab52eda9215fa04e01e03417f9e3b87cba90dc99).
-/
module
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Combinatorics.Hindman
public import Mathlib.Tactic

@[expose] public section
open Set Filter Function TopologicalSpace
open scoped Topology BigOperators

namespace IPTransitive

/-- An IP set contains all nonempty finite sums of one positive sequence. -/
def HasPositiveFiniteSums (A : Set ℕ) : Prop :=
  ∃ p : ℕ → ℕ, (∀ i, 0 < p i) ∧
    ∀ s : Finset ℕ, s.Nonempty → (∑ i ∈ s, p i) ∈ A

/-- Every point of a singleton system visits every nonempty set at all times. -/
theorem singleton_visits_have_positive_finite_sums
    {X : Type*} [Subsingleton X] (f : X → X) (x : X) (U : Set X) (hU : U.Nonempty) :
    HasPositiveFiniteSums {n | f^[n] x ∈ U} := by
  obtain ⟨y, hy⟩ := hU
  refine ⟨fun _ => 1, fun _ => Nat.zero_lt_one, ?_⟩
  intro s hs
  change f^[∑ i ∈ s, (1 : ℕ)] x ∈ U
  have hxy : f^[∑ i ∈ s, (1 : ℕ)] x = y := Subsingleton.elim _ _
  simpa only [hxy] using hy

/-- A dense sequence in a T1 space without isolated points visits each nonempty open set arbitrarily late. -/
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

/-- Extend a finite family of simultaneous return times using positive visits to neighborhoods of y. -/
theorem positive_return_step {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) (x y : X) (U : Set X) (hU : IsOpen U) (hy : y ∈ U)
    (hrec : ∀ V : Set X, IsOpen V → y ∈ V →
      ∃ n : ℕ, 0 < n ∧ f^[n] x ∈ V ∧ f^[n] y ∈ V)
    (S : Finset ℕ) (hS : ∀ s ∈ S, f^[s] y ∈ U) :
    ∃ n : ℕ, 0 < n ∧ f^[n] x ∈ U ∧ f^[n] y ∈ U ∧
      ∀ s ∈ S, f^[n+s] x ∈ U ∧ f^[n+s] y ∈ U := by
  let V : Set X := U ∩ ⋂ s ∈ S, (f^[s]) ⁻¹' U
  have hVopen : IsOpen V := hU.inter (isOpen_biInter_finset fun s _ => hU.preimage (hf.iterate s))
  have hyV : y ∈ V := by
    refine ⟨hy, ?_⟩
    simp only [mem_iInter, mem_preimage]
    exact hS
  obtain ⟨n, hn, hxV, hyV'⟩ := hrec V hVopen hyV
  refine ⟨n, hn, hxV.1, hyV'.1, ?_⟩
  intro s hs
  have hxS := (mem_iInter₂.mp hxV.2) s hs
  have hyS := (mem_iInter₂.mp hyV'.2) s hs
  constructor
  · rw [Nat.add_comm n s, iterate_add_apply]
    exact hxS
  · rw [Nat.add_comm n s, iterate_add_apply]
    exact hyS
/-- Open-set hitting transitivity, including time zero. -/
def OpenTransitive {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ n : ℕ, ∃ z ∈ U, f^[n] z ∈ V

/-- The diagonal action of a map on a pair. -/
def pairMap {X : Type*} (f : X → X) (p : X × X) : X × X := (f p.1, f p.2)

/-- Coordinatewise iteration; compare the prior Furstenberg weak-mixing package. -/
theorem iterate_pairMap {X : Type*} (f : X → X) (n : ℕ) (p : X × X) :
    (pairMap f)^[n] p = (f^[n] p.1, f^[n] p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [iterate_succ_apply, ih, pairMap]

/-- A Hausdorff weakly mixing system with an isolated point is a singleton. -/
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
/-- In a nontrivial Hausdorff weakly mixing system the square has no isolated points. -/
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
/-- A forward orbit is dense, allowing time zero. -/
def DenseOrbit {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  Dense (range (fun n : ℕ => f^[n] x))

/-- Generic dense orbits for a continuous transitive map with a countable basis.
Adapted from the repository's strongly-transitive-sequences package. -/
theorem residual_dense_orbits {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive f) :
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
/-- Dense open product sets have dense sections on a residual set of parameters.
Adapted from the repository's Kuratowski–Ulam package. -/
theorem eventually_dense_sections {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y] {U : Set (X × Y)} (hU : IsOpen U) (hd : Dense U) :
    ∀ᶠ x in residual X, Dense (Prod.mk x ⁻¹' U) := by
  let B : Set (Set Y) := countableBasis Y
  have hBc : B.Countable := countable_countableBasis Y
  have hBo : ∀ V ∈ B, IsOpen V ∧ V.Nonempty := fun V hV =>
    ⟨isOpen_of_mem_countableBasis hV, nonempty_of_mem_countableBasis hV⟩
  have hB : ∀ W : Set Y, IsOpen W → W.Nonempty → ∃ V ∈ B, V ⊆ W := by
    intro W hW ⟨y, hy⟩
    obtain ⟨V, hV, _, hVW⟩ := (isBasis_countableBasis Y).exists_subset_of_mem_open hy hW
    exact ⟨V, hV, hVW⟩
  let G : Set Y → Set X := fun V => Prod.fst '' (U ∩ (univ ×ˢ V))
  have hG : ∀ V ∈ B, G V ∈ residual X := by
    intro V hV
    refine residual_of_dense_open
      (isOpenMap_fst _ (hU.inter (isOpen_univ.prod (hBo V hV).1))) ?_
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ :=
      hd.inter_open_nonempty (W ×ˢ V) (hW.prod (hBo V hV).1)
        (hWne.prod (hBo V hV).2)
    exact ⟨x, hx, (x, y), ⟨hxy, trivial, hy⟩, rfl⟩
  filter_upwards [(eventually_countable_ball hBc).mpr hG] with x hx
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨V, hVB, hVW⟩ := hB W hW hWne
  obtain ⟨⟨x', y⟩, ⟨hxy, _, hy⟩, heq⟩ := hx V hVB
  change x' = x at heq
  subst x'
  exact ⟨y, hVW hy, hxy⟩

/-- Residual sets in a product have residual sections for residually many parameters. -/
theorem eventually_residual_sections {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y] {A : Set (X × Y)} (hA : A ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, Prod.mk x ⁻¹' A ∈ residual Y := by
  obtain ⟨S, hSo, hSd, hSc, hSA⟩ := mem_residual_iff.mp hA
  have hgood : ∀ U ∈ S, ∀ᶠ x in residual X, Prod.mk x ⁻¹' U ∈ residual Y := by
    intro U hU
    filter_upwards [eventually_dense_sections (hSo U hU) (hSd U hU)] with x hx
    exact residual_of_dense_open
      ((hSo U hU).preimage (continuous_const.prodMk continuous_id)) hx
  filter_upwards [(eventually_countable_ball hSc).mpr hgood] with x hx
  have hi : (⋂ U ∈ S, Prod.mk x ⁻¹' U) ∈ residual Y :=
    (countable_bInter_mem hSc).mpr hx
  apply mem_of_superset hi
  intro y hy
  apply hSA
  exact fun U hU => mem_iInter₂.mp hy U hU
/-- Generically, every nonempty open set contains a point with positive
simultaneous visits to its neighborhoods with the parameter point. -/
theorem residual_positive_pair_returns {X : Type*} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] [BaireSpace X] [Nontrivial X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive (pairMap f)) :
    ∀ᶠ x in residual X, ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ y ∈ U, ∀ V : Set X, IsOpen V → y ∈ V →
        ∃ n : ℕ, 0 < n ∧ f^[n] x ∈ V ∧ f^[n] y ∈ V := by
  have hpair : Continuous (pairMap f) :=
    (hf.comp continuous_fst).prodMk (hf.comp continuous_snd)
  have hgood := eventually_residual_sections (residual_dense_orbits (pairMap f) hpair ht)
  filter_upwards [hgood] with x hx U hU hnU
  obtain ⟨y, hyU, hxy⟩ := (dense_of_mem_residual hx).inter_open_nonempty U hU hnU
  refine ⟨y, hyU, ?_⟩
  intro V hV hyV
  have : ∀ z : X × X, NeBot (𝓝[≠] z) := square_punctured_neBot f ht
  obtain ⟨n, hn, hmem⟩ := dense_hits_after
    (fun n : ℕ => (pairMap f)^[n] (x, y)) hxy (V ×ˢ V)
      (hV.prod hV) ⟨(y, y), hyV, hyV⟩ 1
  rw [iterate_pairMap] at hmem
  exact ⟨n, hn, hmem.1, hmem.2⟩
/-- The finite sums generated by the first n entries, including the empty sum. -/
def prefixSums (p : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).powerset.image (fun s => ∑ i ∈ s, p i)

/-- If all prior nonempty sums return y to U, one positive time can extend
all prior sums simultaneously for both x and y. -/
theorem extend_prefix_sums {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) (x y : X) (U : Set X) (hU : IsOpen U) (hy : y ∈ U)
    (hrec : ∀ V : Set X, IsOpen V → y ∈ V →
      ∃ n : ℕ, 0 < n ∧ f^[n] x ∈ V ∧ f^[n] y ∈ V)
    (p : ℕ → ℕ) (n : ℕ)
    (hgood : ∀ s : Finset ℕ, s ⊆ Finset.range n → s.Nonempty →
      f^[∑ i ∈ s, p i] y ∈ U) :
    ∃ k : ℕ, 0 < k ∧ f^[k] x ∈ U ∧ f^[k] y ∈ U ∧
      ∀ s : Finset ℕ, s ⊆ Finset.range n →
        f^[k + ∑ i ∈ s, p i] x ∈ U ∧ f^[k + ∑ i ∈ s, p i] y ∈ U := by
  classical
  have hS : ∀ t ∈ prefixSums p n, f^[t] y ∈ U := by
    intro t ht
    simp only [prefixSums, Finset.mem_image, Finset.mem_powerset] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    by_cases hne : s.Nonempty
    · exact hgood s hs hne
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [he] using hy
  obtain ⟨k, hk, hx, hyk, hnext⟩ := positive_return_step f hf x y U hU hy hrec
    (prefixSums p n) hS
  refine ⟨k, hk, hx, hyk, ?_⟩
  intro s hs
  apply hnext
  simp only [prefixSums, Finset.mem_image, Finset.mem_powerset]
  exact ⟨s, hs, rfl⟩
/-- Prefix invariant used to construct an IP-generating sequence. -/
def PrefixGood {X : Type*} (f : X → X) (x y : X) (U : Set X) (p : ℕ → ℕ) (n : ℕ) : Prop :=
  (∀ i < n, 0 < p i) ∧ ∀ s : Finset ℕ, s ⊆ Finset.range n → s.Nonempty →
    f^[∑ i ∈ s, p i] x ∈ U ∧ f^[∑ i ∈ s, p i] y ∈ U

/-- A good finite prefix extends by one positive generator. -/
theorem extend_good_prefix {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) (x y : X) (U : Set X) (hU : IsOpen U) (hy : y ∈ U)
    (hrec : ∀ V : Set X, IsOpen V → y ∈ V →
      ∃ n : ℕ, 0 < n ∧ f^[n] x ∈ V ∧ f^[n] y ∈ V)
    (p : ℕ → ℕ) (n : ℕ) (hg : PrefixGood f x y U p n) :
    ∃ q : ℕ → ℕ, (∀ i < n, q i = p i) ∧ PrefixGood f x y U q (n+1) := by
  classical
  obtain ⟨k, hk, hxk, hyk, hnext⟩ := extend_prefix_sums f hf x y U hU hy hrec p n
    (fun s hs hne => (hg.2 s hs hne).2)
  let q := Function.update p n k
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i hi
    simp [q, Nat.ne_of_lt hi]
  · intro i hi
    by_cases he : i = n
    · subst i
      simpa [q] using hk
    · have hi' : i < n := by omega
      simpa [q, Function.update, he] using hg.1 i hi'
  · intro s hs hne
    have herase : s.erase n ⊆ Finset.range n := by
      intro i hi
      have his : i ∈ s := Finset.mem_of_mem_erase hi
      have hineq : i ≠ n := Finset.ne_of_mem_erase hi
      have hilt : i < n+1 := Finset.mem_range.mp (hs his)
      exact Finset.mem_range.mpr (by omega)
    by_cases hn : n ∈ s
    · have hsum : (∑ i ∈ s, q i) = k + ∑ i ∈ s.erase n, p i := by
        rw [← Finset.insert_erase hn, Finset.sum_insert (Finset.notMem_erase n s)]
        simp only [q, Function.update_self]
        congr 1
        rw [Finset.erase_insert (Finset.notMem_erase n s)]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≠ n := Finset.ne_of_mem_erase hi
        simp [Function.update, hi']
      rw [hsum]
      exact hnext (s.erase n) herase
    · have hsmall : s ⊆ Finset.range n := by
        intro i hi
        have hilt : i < n+1 := Finset.mem_range.mp (hs hi)
        have hne' : i ≠ n := fun h => hn (h ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      have hsum : (∑ i ∈ s, q i) = ∑ i ∈ s, p i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hilt : i < n := Finset.mem_range.mp (hsmall hi)
        simp [q, Nat.ne_of_lt hilt]
      rw [hsum]
      exact hg.2 s hsmall hne
/-- Positive simultaneous neighborhood returns generate an IP set of visits. -/
theorem positive_pair_returns_yield_ip {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) (x y : X) (U : Set X) (hU : IsOpen U) (hy : y ∈ U)
    (hrec : ∀ V : Set X, IsOpen V → y ∈ V →
      ∃ n : ℕ, 0 < n ∧ f^[n] x ∈ V ∧ f^[n] y ∈ V) :
    HasPositiveFiniteSums {n | f^[n] x ∈ U} := by
  classical
  have start : PrefixGood f x y U (fun _ => 0) 0 := by
    constructor
    · intro i hi; omega
    · intro s hs hne
      have he : s = ∅ := Finset.subset_empty.mp (by simpa using hs)
      exact False.elim (hne.ne_empty he)
  let stages : (n : ℕ) → {p : ℕ → ℕ // PrefixGood f x y U p n} := fun n =>
    Nat.rec ⟨fun _ => 0, start⟩
      (fun n st => ⟨Classical.choose (extend_good_prefix f hf x y U hU hy hrec st.1 n st.2),
        (Classical.choose_spec (extend_good_prefix f hf x y U hU hy hrec st.1 n st.2)).2⟩) n
  have step (n i : ℕ) (hi : i < n) : (stages (n+1)).1 i = (stages n).1 i := by
    exact (Classical.choose_spec (extend_good_prefix f hf x y U hU hy hrec
      (stages n).1 n (stages n).2)).1 i hi
  have stable (a b i : ℕ) (hab : a ≤ b) (hi : i < a) :
      (stages b).1 i = (stages a).1 i := by
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [step m i (by omega)]
      exact ih
  let p : ℕ → ℕ := fun i => (stages (i+1)).1 i
  refine ⟨p, ?_, ?_⟩
  · intro i
    exact (stages (i+1)).2.1 i (Nat.lt_succ_self i)
  · intro s hne
    let n := s.sup id + 1
    have hs : s ⊆ Finset.range n := by
      intro i hi
      have hle : i ≤ s.sup id := Finset.le_sup (f := id) hi
      exact Finset.mem_range.mpr (by dsimp [n]; omega)
    have hsum : (∑ i ∈ s, p i) = ∑ i ∈ s, (stages n).1 i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i < n := Finset.mem_range.mp (hs hi)
      exact (stable (i+1) n i (by omega) (Nat.lt_succ_self i)).symm
    rw [hsum]
    exact ((stages n).2.2 s hs hne).1
/-- Every nonempty open set has an IP set of entering times from x. -/
def IsIPTransitivePoint {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → HasPositiveFiniteSums {n | f^[n] x ∈ U}

/-- Weak mixing implies generic IP-transitivity. Time zero is allowed in
open-set transitivity, but the generated IP sequence consists of positive times. -/
theorem residual_ip_transitive {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [BaireSpace X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive (pairMap f)) :
    {x : X | IsIPTransitivePoint f x} ∈ residual X := by
  classical
  by_cases hsub : Subsingleton X
  · have : Subsingleton X := hsub
    refine mem_of_superset univ_mem ?_
    intro x hx U hU hnU
    exact singleton_visits_have_positive_finite_sums f x U hnU
  · have : Nontrivial X := not_subsingleton_iff_nontrivial.mp hsub
    filter_upwards [residual_positive_pair_returns f hf ht] with x hx
    intro U hU hnU
    obtain ⟨y, hyU, hrec⟩ := hx U hU hnU
    exact positive_pair_returns_yield_ip f hf x y U hU hyU hrec

/-- A nonempty Baire system has a nonempty dense G-delta family of IP-transitive points. -/
theorem exists_dense_Gdelta_ip_transitive {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [BaireSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive (pairMap f)) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧ C.Nonempty ∧ ∀ x ∈ C, IsIPTransitivePoint f x := by
  obtain ⟨C, hC, hG, hd⟩ := mem_residual.mp (residual_ip_transitive f hf ht)
  exact ⟨C, hG, hd, hd.nonempty, hC⟩
end IPTransitive
