/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Developed with substantive OpenAI Codex assistance; no human review claimed.
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Separation.Lemmas
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.CantorScheme
public import Mathlib.Order.PiLex
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Topology.Instances.Rat

/-!
# Sierpiński's characterization of the rationals

Source: Michael Francis, arXiv:1210.1008, Theorem 2. The construction uses
scheduled clopen splits, rather than the source's translation in a Cantor group.
Binary coding infrastructure is adapted from the campaign's Cantor package
at ea2e84471cdd230fd133a9e2e3b0dfc25e1a7f0f (Apache-2.0).
-/

@[expose] public section
noncomputable section
open Set Function Filter Topology TopologicalSpace

namespace SierpinskiRationals

def HasClopenBasis (X : Type*) [TopologicalSpace X] : Prop :=
  IsTopologicalBasis {U : Set X | IsClopen U}

/-- Countability and metrizability imply a clopen basis; it is not an extra hypothesis. -/
theorem countable_hasClopenBasis (X : Type*) [TopologicalSpace X]
    [Countable X] [MetrizableSpace X] : HasClopenBasis X := by
  let := TopologicalSpace.metrizableSpaceMetric X
  exact CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum
    ((Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt Cardinal.aleph0_lt_continuum)

/-- Every nonempty open set has a point outside any prescribed finite set. -/
theorem exists_mem_open_avoiding {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) (F : Finset X) :
    ∃ x ∈ U, x ∉ F := by
  obtain ⟨x, hx⟩ := hne
  have hi : U.Infinite := infinite_of_mem_nhds x (hU.mem_nhds hx)
  obtain ⟨y, hyU, hyF⟩ := hi.exists_notMem_finite F.finite_toSet
  exact ⟨y, hyU, hyF⟩

/-- A clopen cell splits while keeping every protected point in either requested child. -/
theorem exists_protected_split {X : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] (hB : HasClopenBasis X) {U : Set X}
    (hU : IsClopen U) (hne : U.Nonempty) (F : Finset X) (b : Bool) :
    ∃ V : Bool → Set X, (V false ∪ V true = U) ∧ Disjoint (V false) (V true) ∧
      (∀ c, IsClopen (V c) ∧ (V c).Nonempty) ∧ (∀ x ∈ F, x ∈ U → x ∈ V b) := by
  classical
  obtain ⟨u, hu, huF⟩ := exists_mem_open_avoiding hU.isOpen hne F
  obtain ⟨v, hv, hvu⟩ := preperfect_iff_nhds.mp hU.isOpen.preperfect u hu U
    (hU.isOpen.mem_nhds hu)
  obtain ⟨W, hW, huW, hWU⟩ := hB.exists_subset_of_mem_open
    (show u ∈ U \ (↑F ∪ {v} : Set X) from ⟨hu, by simpa [huF, ne_comm] using hvu⟩)
    (hU.isOpen.sdiff (F.finite_toSet.union (finite_singleton v)).isClosed)
  have hWsub : W ⊆ U := fun _ h => (hWU h).1
  have hvW : v ∉ W := fun h => (hWU h).2 (Or.inr (mem_singleton v))
  have hcover : W ∪ (U \ W) = U := by
    ext x
    simp only [mem_union, Set.mem_sdiff]
    constructor
    · rintro (hx | hx)
      · exact hWsub hx
      · exact hx.1
    · intro hx
      by_cases hw : x ∈ W
      · exact Or.inl hw
      · exact Or.inr ⟨hx, hw⟩
  have hprotected : ∀ x ∈ F, x ∈ U → x ∈ U \ W := by
    intro x hx hxU
    exact ⟨hxU, fun h => (hWU h).2 (Or.inl hx)⟩
  cases b
  · refine ⟨fun c => if c then W else U \ W, ?_, ?_, ?_, hprotected⟩
    · simpa [union_comm] using hcover
    · exact disjoint_sdiff_left
    · intro c
      cases c
      · exact ⟨hU.diff hW, v, hv.1, hvW⟩
      · exact ⟨hW, u, huW⟩
  · refine ⟨fun c => if c then U \ W else W, hcover, disjoint_sdiff_right, ?_, hprotected⟩
    intro c
    cases c
    · exact ⟨hW, u, huW⟩
    · exact ⟨hU.diff hW, v, hv.1, hvW⟩

/-- A clopen cell can also split to decide one basis element. -/
theorem exists_deciding_split {X : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] (hB : HasClopenBasis X) {U C : Set X}
    (hU : IsClopen U) (hne : U.Nonempty) (hC : IsClopen C) :
    ∃ V : Bool → Set X, (V false ∪ V true = U) ∧ Disjoint (V false) (V true) ∧
      ∀ b, IsClopen (V b) ∧ (V b).Nonempty ∧ (V b ⊆ C ∨ V b ⊆ Cᶜ) := by
  classical
  by_cases h0 : (U ∩ C).Nonempty
  · by_cases h1 : (U \ C).Nonempty
    · refine ⟨fun b => if b then U \ C else U ∩ C, ?_, ?_, ?_⟩
      · ext x
        simp only [Bool.false_eq_true, ↓reduceIte, mem_union, mem_inter_iff, Set.mem_sdiff]
        tauto
      · exact disjoint_left.mpr fun _ hx hy => hy.2 hx.2
      · intro b
        cases b
        · exact ⟨hU.inter hC, h0, Or.inl inter_subset_right⟩
        · exact ⟨hU.diff hC, h1, Or.inr (sdiff_subset_compl U C)⟩
    · obtain ⟨V, hc, hd, hV, _⟩ := exists_protected_split hB hU hne ∅ false
      have huC : U ⊆ C := by
        intro x hx
        by_contra hn
        exact h1 ⟨x, hx, hn⟩
      refine ⟨V, hc, hd, fun b => ⟨(hV b).1, (hV b).2, Or.inl (?_)⟩⟩
      cases b
      · exact subset_union_left.trans (hc.subset.trans huC)
      · exact subset_union_right.trans (hc.subset.trans huC)
  · obtain ⟨V, hc, hd, hV, _⟩ := exists_protected_split hB hU hne ∅ false
    have huC : U ⊆ Cᶜ := by
      intro x hx hxC
      exact h0 ⟨x, hx, hxC⟩
    refine ⟨V, hc, hd, fun b => ⟨(hV b).1, (hV b).2, Or.inr (?_)⟩⟩
    cases b
    · exact subset_union_left.trans (hc.subset.trans huC)
    · exact subset_union_right.trans (hc.subset.trans huC)

/-- Three stages: decide a basis set, retain the first points to the left,
then retain them to the right. All children remain nonempty. -/
def StepProperty {X : Type*} (B : ℕ → Set X) (E : ℕ → X) (n : ℕ)
    (U : Set X) (V : Bool → Set X) : Prop :=
  (n % 3 = 0 → ∀ b, V b ⊆ B (n / 3) ∨ V b ⊆ (B (n / 3))ᶜ) ∧
  (n % 3 = 1 → ∀ k ≤ n / 3, E k ∈ U → E k ∈ V false) ∧
  (n % 3 = 2 → ∀ k ≤ n / 3, E k ∈ U → E k ∈ V true)

structure BinaryScheme (X : Type*) [TopologicalSpace X] (B : ℕ → Set X) (E : ℕ → X) where
  sets : List Bool → Set X
  root : sets [] = univ
  clopen : ∀ l, IsClopen (sets l)
  nonempty : ∀ l, (sets l).Nonempty
  cover : ∀ l, sets (false :: l) ∪ sets (true :: l) = sets l
  disjoint : ∀ l, Disjoint (sets (false :: l)) (sets (true :: l))
  step : ∀ l, StepProperty B E l.length (sets l) (fun b => sets (b :: l))

theorem exists_binary_scheme {X : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] [Nonempty X] (hB : HasClopenBasis X)
    (B : ℕ → Set X) (hcl : ∀ n, IsClopen (B n)) (E : ℕ → X) :
    Nonempty (BinaryScheme X B E) := by
  classical
  let P := {U : Set X // IsClopen U ∧ U.Nonempty}
  have split : ∀ n (U : P), ∃ V : Bool → Set X,
      (V false ∪ V true = U.val) ∧ Disjoint (V false) (V true) ∧
      (∀ b, IsClopen (V b) ∧ (V b).Nonempty) ∧ StepProperty B E n U.val V := by
    intro n U
    by_cases h0 : n % 3 = 0
    · obtain ⟨V, hc, hd, hV⟩ := exists_deciding_split hB U.property.1 U.property.2 (hcl (n / 3))
      exact ⟨V, hc, hd, fun b => ⟨(hV b).1, (hV b).2.1⟩,
        (fun _ b => (hV b).2.2), (by omega), (by omega)⟩
    · by_cases h1 : n % 3 = 1
      · obtain ⟨V, hc, hd, hV, hp⟩ := exists_protected_split hB U.property.1 U.property.2
          ((Finset.range (n / 3 + 1)).image E) false
        refine ⟨V, hc, hd, hV, (by omega), ?_, (by omega)⟩
        intro _ k hk hUk
        exact hp (E k) (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩) hUk
      · obtain ⟨V, hc, hd, hV, hp⟩ := exists_protected_split hB U.property.1 U.property.2
          ((Finset.range (n / 3 + 1)).image E) true
        refine ⟨V, hc, hd, hV, (by omega), (by omega), ?_⟩
        intro _ k hk hUk
        exact hp (E k) (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩) hUk
  choose V hcover hd hV hs using split
  let D : List Bool → P := fun l => List.rec
    ⟨univ, isClopen_univ, Set.univ_nonempty⟩
    (fun b l U => ⟨V l.length U b, (hV l.length U b).1, (hV l.length U b).2⟩) l
  exact ⟨{
    sets := fun l => (D l).val
    root := rfl
    clopen := fun l => (D l).property.1
    nonempty := fun l => (D l).property.2
    cover := fun l => hcover l.length (D l)
    disjoint := fun l => hd l.length (D l)
    step := fun l => hs l.length (D l) }⟩

namespace BinaryScheme
variable {X : Type*} [TopologicalSpace X] {B : ℕ → Set X} {E : ℕ → X}
    (S : BinaryScheme X B E)

theorem child_subset (l : List Bool) (b : Bool) : S.sets (b :: l) ⊆ S.sets l := by
  cases b
  · exact subset_union_left.trans (S.cover l).subset
  · exact subset_union_right.trans (S.cover l).subset

def next (x : X) (l : List Bool) : Bool := by
  classical
  exact decide (x ∈ S.sets (true :: l))

def addressPrefix (x : X) (n : ℕ) : List Bool :=
  Nat.rec [] (fun _ l => S.next x l :: l) n

def code (x : X) (n : ℕ) : Bool := S.next x (S.addressPrefix x n)

theorem res_code (x : X) (n : ℕ) : PiNat.res (S.code x) n = S.addressPrefix x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PiNat.res_succ, ih]; rfl

theorem next_mem {x : X} {l : List Bool} (hx : x ∈ S.sets l) :
    x ∈ S.sets (S.next x l :: l) := by
  classical
  by_cases ht : x ∈ S.sets (true :: l)
  · simp [next, ht]
  · have hm : x ∈ S.sets (false :: l) ∪ S.sets (true :: l) := (S.cover l).symm ▸ hx
    simpa [next, ht] using hm.resolve_right ht

theorem addressPrefix_mem (x : X) (n : ℕ) : x ∈ S.sets (S.addressPrefix x n) := by
  induction n with
  | zero => simp [addressPrefix, S.root]
  | succ n ih => exact S.next_mem ih

theorem code_mem (x : X) (n : ℕ) : x ∈ S.sets (PiNat.res (S.code x) n) := by
  rw [S.res_code]
  exact S.addressPrefix_mem x n

theorem res_code_of_mem {x : X} (l : List Bool) (hx : x ∈ S.sets l) :
    PiNat.res (S.code x) l.length = l := by
  classical
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hp := S.child_subset l b hx
    have hl := ih hp
    have he : S.addressPrefix x l.length = l := (S.res_code x l.length).symm.trans hl
    rw [List.length_cons, PiNat.res_succ, hl]
    have hb : S.next x l = b := by
      cases b
      · have ht : x ∉ S.sets (true :: l) := fun ht => disjoint_left.mp (S.disjoint l) hx ht
        simp [next, ht]
      · simp [next, hx]
    simp only [code, he, hb]

theorem continuous_code : Continuous S.code := by
  apply continuous_pi
  intro n
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_const.congr
  filter_upwards [(S.clopen (PiNat.res (S.code x) (n + 1))).isOpen.mem_nhds (S.code_mem x (n + 1))] with y hy
  have he : PiNat.res (S.code y) (n + 1) = PiNat.res (S.code x) (n + 1) := by
    simpa only [PiNat.res_length] using S.res_code_of_mem _ hy
  exact (PiNat.res_eq_res.mp he (Nat.lt_succ_self n)).symm

theorem decides_basis (x : X) (n : ℕ) :
    S.sets (PiNat.res (S.code x) (3 * n + 1)) ⊆ B n ∨
    S.sets (PiNat.res (S.code x) (3 * n + 1)) ⊆ (B n)ᶜ := by
  have h := (S.step (PiNat.res (S.code x) (3 * n))).1
  simpa [PiNat.res_succ, PiNat.res_length] using h (by simp) (S.code x (3 * n))

theorem injective_code [T2Space X] (hB : IsTopologicalBasis (range B)) : Injective S.code := by
  intro x y he
  by_contra hxy
  obtain ⟨U, ⟨n, rfl⟩, hxU, hsub⟩ := hB.exists_subset_of_mem_open
    (show x ∈ ({y} : Set X)ᶜ from hxy) isOpen_compl_singleton
  have hx := S.code_mem x (3 * n + 1)
  have hy := S.code_mem y (3 * n + 1)
  rw [← he] at hy
  rcases S.decides_basis x n with hd | hd
  · exact hsub (hd hy) rfl
  · exact hd hx hxU

theorem code_has_both_bits (hE : Surjective E) (x : X) (N : ℕ) (b : Bool) :
    ∃ n ≥ N, S.code x n = b := by
  obtain ⟨k, rfl⟩ := hE x
  let m := max k N
  cases b
  · let n := 3 * m + 1
    have hp := (S.step (PiNat.res (S.code (E k)) n)).2.1
    have hx : E k ∈ S.sets (false :: PiNat.res (S.code (E k)) n) := by
      apply hp
      · simp only [PiNat.res_length]; dsimp [n]; omega
      · simp only [PiNat.res_length]; dsimp [n, m]; omega
      · exact S.code_mem _ _
    have he := S.res_code_of_mem _ hx
    have hn : S.code (E k) n = false := by
      exact (List.cons.inj (by simpa only [List.length_cons, PiNat.res_length, PiNat.res_succ] using he)).1
    exact ⟨n, by dsimp [n, m]; omega, hn⟩
  · let n := 3 * m + 2
    have hp := (S.step (PiNat.res (S.code (E k)) n)).2.2
    have hx : E k ∈ S.sets (true :: PiNat.res (S.code (E k)) n) := by
      apply hp
      · simp only [PiNat.res_length]; dsimp [n]; omega
      · simp only [PiNat.res_length]; dsimp [n, m]; omega
      · exact S.code_mem _ _
    have he := S.res_code_of_mem _ hx
    have hn : S.code (E k) n = true := by
      exact (List.cons.inj (by simpa only [List.length_cons, PiNat.res_length, PiNat.res_succ] using he)).1
    exact ⟨n, by dsimp [n, m]; omega, hn⟩

theorem exists_opposite (x : X) (n : ℕ) (b : Bool) :
    ∃ y, (∀ k < n, S.code y k = S.code x k) ∧ S.code y n = b := by
  obtain ⟨y, hy⟩ := S.nonempty (b :: PiNat.res (S.code x) n)
  have he := S.res_code_of_mem _ hy
  have he' : S.code y n :: PiNat.res (S.code y) n = b :: PiNat.res (S.code x) n := by
    simpa only [List.length_cons, PiNat.res_length, PiNat.res_succ] using he
  exact ⟨y, PiNat.res_eq_res.mp (List.cons.inj he').2, (List.cons.inj he').1⟩

/-- Points on both sides exist inside every finite-prefix neighborhood. -/
theorem exists_lex_neighbors (hE : Surjective E) (x : X) (N : ℕ) :
    ∃ a b, toLex (S.code a) < toLex (S.code x) ∧ toLex (S.code x) < toLex (S.code b) ∧
      (∀ k < N, S.code a k = S.code x k) ∧ (∀ k < N, S.code b k = S.code x k) := by
  obtain ⟨n, hn, hxn⟩ := S.code_has_both_bits hE x N true
  obtain ⟨a, ha, han⟩ := S.exists_opposite x n false
  obtain ⟨m, hm, hxm⟩ := S.code_has_both_bits hE x N false
  obtain ⟨b, hb, hbm⟩ := S.exists_opposite x m true
  refine ⟨a, b, ?_, ?_, fun k hk => ha k (by omega), fun k hk => hb k (by omega)⟩
  · exact ⟨n, ha, by simp [han, hxn]⟩
  · exact ⟨m, fun k hk => (hb k hk).symm, by simp [hxm, hbm]⟩

theorem isOpen_lex_left (v : X) : IsOpen {x | toLex (S.code x) < toLex (S.code v)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨n, hpre, hlt⟩ := hx
  apply Filter.mem_of_superset
    ((S.clopen (PiNat.res (S.code x) (n + 1))).isOpen.mem_nhds (S.code_mem x (n + 1)))
  intro y hy
  have he : ∀ k < n + 1, S.code y k = S.code x k := PiNat.res_eq_res.mp (by
    simpa only [PiNat.res_length] using S.res_code_of_mem _ hy)
  exact ⟨n, fun k hk => (he k (by omega)).trans (hpre k hk), by simpa only [Pi.toLex_apply, he n (by omega)] using hlt⟩

theorem isOpen_lex_right (v : X) : IsOpen {x | toLex (S.code v) < toLex (S.code x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨n, hpre, hlt⟩ := hx
  apply Filter.mem_of_superset
    ((S.clopen (PiNat.res (S.code x) (n + 1))).isOpen.mem_nhds (S.code_mem x (n + 1)))
  intro y hy
  have he : ∀ k < n + 1, S.code y k = S.code x k := PiNat.res_eq_res.mp (by
    simpa only [PiNat.res_length] using S.res_code_of_mem _ hy)
  exact ⟨n, fun k hk => (hpre k hk).trans (he k (by omega)).symm, by simpa only [Pi.toLex_apply, he n (by omega)] using hlt⟩

/-- Lexicographic intervals between two points sharing a prefix retain that prefix. -/
theorem prefix_of_between {a b x y : ℕ → Bool} {N : ℕ}
    (ha : ∀ k < N, a k = x k) (hb : ∀ k < N, b k = x k)
    (hay : toLex a ≤ toLex y) (hyb : toLex y ≤ toLex b) : ∀ k < N, y k = x k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hleft : a k ≤ y k := Pi.apply_le_of_toLex hay (fun j hj =>
      (ha j (by omega)).trans (ih j hj (by omega)).symm)
    have hright : y k ≤ b k := Pi.apply_le_of_toLex hyb (fun j hj =>
      (ih j hj (by omega)).trans (hb j (by omega)).symm)
    rw [ha k hk] at hleft
    rw [hb k hk] at hright
    exact le_antisymm hright hleft

/-- The order is pulled back from addresses, rather than assumed as input. -/
@[instance_reducible] def codeOrder [T2Space X] (hB : IsTopologicalBasis (range B)) : LinearOrder X :=
  LinearOrder.lift' (fun x => toLex (S.code x)) (fun _ _ h => S.injective_code hB h)

theorem codeOrder_noMin [T2Space X] (hB : IsTopologicalBasis (range B)) (hE : Surjective E) :
    @NoMinOrder X (S.codeOrder hB).toLT := by
  let := S.codeOrder hB
  constructor
  intro x
  obtain ⟨a, b, ha, _, _, _⟩ := S.exists_lex_neighbors hE x 0
  exact ⟨a, ha⟩

theorem codeOrder_noMax [T2Space X] (hB : IsTopologicalBasis (range B)) (hE : Surjective E) :
    @NoMaxOrder X (S.codeOrder hB).toLT := by
  let := S.codeOrder hB
  constructor
  intro x
  obtain ⟨a, b, _, hb, _, _⟩ := S.exists_lex_neighbors hE x 0
  exact ⟨b, hb⟩

theorem codeOrder_dense [T2Space X] (hB : IsTopologicalBasis (range B)) (hE : Surjective E) :
    @DenselyOrdered X (S.codeOrder hB).toLT := by
  let := S.codeOrder hB
  constructor
  intro x y hxy
  obtain ⟨n, hpre, hlt⟩ := hxy
  obtain ⟨a, b, _, hxb, _, hb⟩ := S.exists_lex_neighbors hE x (n + 1)
  refine ⟨b, hxb, ?_⟩
  exact ⟨n, fun k hk => (hb k (by omega)).trans (hpre k hk), by simpa only [Pi.toLex_apply, hb n (by omega)] using hlt⟩

/-- The constructed order's topology is exactly the original supplied topology. -/
theorem codeOrder_topology [T2Space X] (hB : IsTopologicalBasis (range B))
    (hE : Surjective E) : @OrderTopology X _ (S.codeOrder hB).toPreorder := by
  let := S.codeOrder hB
  have hlocal : ∀ U : Set X, IsOpen U → ∀ x ∈ U,
      ∃ a b, a < x ∧ x < b ∧ Ioo a b ⊆ U := by
    intro U hU x hx
    obtain ⟨_, ⟨n, rfl⟩, hxn, hnU⟩ := hB.exists_subset_of_mem_open hx hU
    rcases S.decides_basis x n with hd | hd
    · obtain ⟨a, b, hax, hxb, ha, hb⟩ := S.exists_lex_neighbors hE x (3 * n + 1)
      refine ⟨a, b, hax, hxb, ?_⟩
      intro y hy
      apply hnU
      apply hd
      have he := prefix_of_between ha hb hy.1.le hy.2.le
      have heq : PiNat.res (S.code y) (3 * n + 1) = PiNat.res (S.code x) (3 * n + 1) :=
        PiNat.res_eq_res.mpr he
      exact heq ▸ S.code_mem y _
    · exact False.elim (hd (S.code_mem x _) hxn)
  constructor
  apply le_antisymm
  · apply le_generateFrom
    rintro U ⟨x, rfl | rfl⟩
    · exact S.isOpen_lex_right x
    · exact S.isOpen_lex_left x
  · intro U hU
    have hloc := hlocal U hU
    let t := Preorder.topology X
    have : @OrderTopology X t _ := ⟨rfl⟩
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨a, b, hax, hxb, hsub⟩ := hloc x hx
    exact Filter.mem_of_superset (Ioo_mem_nhds hax hxb) hsub

end BinaryScheme

/-- Enumerate a clopen basis without changing the supplied topology. -/
theorem exists_countable_clopen_basis (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [Nonempty X] (hB : HasClopenBasis X) :
    ∃ B : ℕ → Set X, (∀ n, IsClopen (B n)) ∧ IsTopologicalBasis (range B) := by
  classical
  obtain ⟨s, hsub, hc, hb⟩ := hB.exists_countable
  have hs : s.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨U, hU, _, _⟩ := hb.exists_subset_of_mem_open (mem_univ x) isOpen_univ
    exact ⟨U, hU⟩
  obtain ⟨f, hf⟩ := hc.exists_surjective hs
  have hr : range (fun n => (f n).val) = s := by
    ext U
    constructor
    · rintro ⟨n, rfl⟩
      exact (f n).property
    · intro hU
      obtain ⟨n, hn⟩ := hf ⟨U, hU⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  exact ⟨fun n => (f n).val, fun n => hsub (f n).property, hr.symm ▸ hb⟩

/-- Sierpiński's characterization, sufficient direction for an arbitrary supplied topology. -/
theorem nonempty_homeomorph (X : Type*) [TopologicalSpace X] [Countable X]
    [MetrizableSpace X] [PerfectSpace X] [Nonempty X] : Nonempty (X ≃ₜ ℚ) := by
  let := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨B, hcl, hb⟩ := exists_countable_clopen_basis X (countable_hasClopenBasis X)
  obtain ⟨E, hE⟩ := exists_surjective_nat X
  obtain ⟨S⟩ := exists_binary_scheme (countable_hasClopenBasis X) B hcl E
  let := S.codeOrder hb
  have := S.codeOrder_noMin hb hE
  have := S.codeOrder_noMax hb hE
  have := S.codeOrder_dense hb hE
  have := S.codeOrder_topology hb hE
  obtain ⟨e⟩ := Order.iso_of_countable_dense X ℚ
  exact ⟨e.toHomeomorph⟩

/-- The usual rational topology has no isolated points. -/
theorem rat_perfectSpace : PerfectSpace ℚ := by
  constructor
  rw [preperfect_iff_nhds]
  intro x _ U hU
  obtain ⟨a, b, hx, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  obtain ⟨y, hxy, hyb⟩ := exists_between hx.2
  exact ⟨y, ⟨hsub ⟨hx.1.trans hxy, hyb⟩, mem_univ _⟩, ne_of_gt hxy⟩

/-- Absence of isolated points transports through a homeomorphism. -/
theorem perfectSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PerfectSpace Y] (e : X ≃ₜ Y) : PerfectSpace X := by
  constructor
  rw [preperfect_iff_nhds]
  intro x _ U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨y, hy, hyx⟩ := preperfect_iff_nhds.mp PerfectSpace.univ_preperfect
    (e x) (mem_univ _) (e '' V) ((e.isOpenMap V hV).mem_nhds (mem_image_of_mem e hxV))
  obtain ⟨z, hz, rfl⟩ := hy.1
  exact ⟨z, ⟨hVU hz, mem_univ _⟩, fun h => hyx (congrArg e h)⟩

/-- Full intrinsic characterization of the rationals with their usual topology. -/
theorem nonempty_homeomorph_iff (X : Type*) [TopologicalSpace X] :
    Nonempty (X ≃ₜ ℚ) ↔ Nonempty X ∧ Countable X ∧ MetrizableSpace X ∧ PerfectSpace X := by
  constructor
  · rintro ⟨e⟩
    have := rat_perfectSpace
    exact ⟨e.toEquiv.nonempty, e.injective.countable, e.isEmbedding.metrizableSpace,
      perfectSpace_of_homeomorph e⟩
  · rintro ⟨hne, hc, hm, hp⟩
    have := hne
    have := hc
    have := hm
    have := hp
    exact nonempty_homeomorph X

end SierpinskiRationals
