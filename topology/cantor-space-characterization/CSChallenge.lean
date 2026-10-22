/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Developed with substantive OpenAI Codex assistance; no human review claimed.
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.CantorScheme

/-!
# Brouwer characterization of Cantor space

Classical source: Anush Tserunyan, Introduction to descriptive set theory,
Theorem 5.3. The proof here uses a binary clopen scheme that decides an
enumerated basis, rather than prescribing diameter reduction at each split.
-/

@[expose] public section
noncomputable section
open Set Function Filter Topology TopologicalSpace

namespace CantorCharacterization

/-- Zero-dimensionality is the existence of a basis consisting of clopen sets. -/
def HasClopenBasis (X : Type*) [TopologicalSpace X] : Prop :=
  IsTopologicalBasis {U : Set X | IsClopen U}

/-- A nonempty open set in a perfect space contains two distinct points. -/
theorem nontrivial_of_nonempty_open {X : Type*} [TopologicalSpace X] [PerfectSpace X]
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) : U.Nontrivial := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hyx⟩ := preperfect_iff_nhds.mp hU.preperfect x hx U (hU.mem_nhds hx)
  exact ⟨y, hy.1, x, hx, hyx⟩

/-- Every nonempty clopen cell has a genuine two-piece clopen partition. -/
theorem exists_clopen_split {X : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] (hB : HasClopenBasis X) {U : Set X}
    (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ V W : Set X, IsClopen V ∧ IsClopen W ∧ V.Nonempty ∧ W.Nonempty ∧
      Disjoint V W ∧ V ∪ W = U := by
  obtain ⟨x, hx, y, hy, hxy⟩ := nontrivial_of_nonempty_open hU.isOpen hne
  obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_subset_of_mem_open
    (show x ∈ U \ {y} from ⟨hx, hxy⟩) (hU.isOpen.inter isOpen_compl_singleton)
  refine ⟨V, U \ V, hV, hU.diff hV, ⟨x, hxV⟩, ⟨y, hy, ?_⟩, disjoint_sdiff_right, ?_⟩
  · intro hyV
    exact (hVU hyV).2 rfl
  · ext z
    constructor
    · rintro (hz | hz)
      · exact (hVU hz).1
      · exact hz.1
    · intro hz
      by_cases hzV : z ∈ V
      · exact Or.inl hzV
      · exact Or.inr ⟨hz, hzV⟩

/-- A binary split can decide any prescribed clopen set, even when that set
is already constant on the parent cell. -/
theorem exists_deciding_split {X : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] (hB : HasClopenBasis X) {U C : Set X}
    (hU : IsClopen U) (hne : U.Nonempty) (hC : IsClopen C) :
    ∃ V : Bool → Set X, (V false ∪ V true = U) ∧ Disjoint (V false) (V true) ∧
      ∀ b, IsClopen (V b) ∧ (V b).Nonempty ∧
        (V b ⊆ C ∨ V b ⊆ Cᶜ) := by
  classical
  by_cases h0 : (U ∩ C).Nonempty
  · by_cases h1 : (U \ C).Nonempty
    · refine ⟨fun b => if b then U \ C else U ∩ C, ?_, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        ext x
        simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
        tauto
      · exact disjoint_left.mpr fun _ hx hy => hy.2 hx.2
      · intro b
        cases b
        · exact ⟨hU.inter hC, h0, Or.inl inter_subset_right⟩
        · exact ⟨hU.diff hC, h1, Or.inr (sdiff_subset_compl U C)⟩
    · obtain ⟨V, W, hV, hW, hnV, hnW, hd, hc⟩ := exists_clopen_split hB hU hne
      have huC : U ⊆ C := by
        intro x hx
        by_contra hn
        exact h1 ⟨x, hx, hn⟩
      refine ⟨fun b => if b then W else V, hc, hd, ?_⟩
      intro b
      cases b
      · exact ⟨hV, hnV, Or.inl (subset_union_left.trans (hc.subset.trans huC))⟩
      · exact ⟨hW, hnW, Or.inl (subset_union_right.trans (hc.subset.trans huC))⟩
  · obtain ⟨V, W, hV, hW, hnV, hnW, hd, hc⟩ := exists_clopen_split hB hU hne
    have huC : U ⊆ Cᶜ := by
      intro x hx hxC
      exact h0 ⟨x, hx, hxC⟩
    refine ⟨fun b => if b then W else V, hc, hd, ?_⟩
    intro b
    cases b
    · exact ⟨hV, hnV, Or.inr (subset_union_left.trans (hc.subset.trans huC))⟩
    · exact ⟨hW, hnW, Or.inr (subset_union_right.trans (hc.subset.trans huC))⟩

/-- A covering binary clopen scheme which decides its enumerated basis in order. -/
structure BinaryScheme (X : Type*) [TopologicalSpace X] (B : ℕ → Set X) where
  sets : List Bool → Set X
  root : sets [] = univ
  clopen : ∀ l, IsClopen (sets l)
  nonempty : ∀ l, (sets l).Nonempty
  cover : ∀ l, sets (false :: l) ∪ sets (true :: l) = sets l
  disjoint : ∀ l, Disjoint (sets (false :: l)) (sets (true :: l))
  decides : ∀ l b, sets (b :: l) ⊆ B l.length ∨ sets (b :: l) ⊆ (B l.length)ᶜ

/-- Existence of a full binary scheme. Perfectness supplies a genuine split
whenever the next basis element does not split the current cell. -/
theorem exists_binary_scheme {X : Type*} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] [Nonempty X] (hB : HasClopenBasis X)
    (B : ℕ → Set X) (hcl : ∀ n, IsClopen (B n)) : Nonempty (BinaryScheme X B) := by
  classical
  let P := {U : Set X // IsClopen U ∧ U.Nonempty}
  have split : ∀ n (U : P), ∃ V : Bool → Set X,
      (V false ∪ V true = U.val) ∧ Disjoint (V false) (V true) ∧
      ∀ b, IsClopen (V b) ∧ (V b).Nonempty ∧
        (V b ⊆ B n ∨ V b ⊆ (B n)ᶜ) := fun n U =>
    exists_deciding_split hB U.property.1 U.property.2 (hcl n)
  choose V hcover hd hV using split
  let D : List Bool → P := fun l => List.rec
    ⟨univ, isClopen_univ, Set.univ_nonempty⟩
    (fun b l U => ⟨V l.length U b, (hV l.length U b).1, (hV l.length U b).2.1⟩) l
  exact ⟨{
    sets := fun l => (D l).val
    root := rfl
    clopen := fun l => (D l).property.1
    nonempty := fun l => (D l).property.2
    cover := fun l => hcover l.length (D l)
    disjoint := fun l => hd l.length (D l)
    decides := fun l b => (hV l.length (D l) b).2.2 }⟩

namespace BinaryScheme
variable {X : Type*} [TopologicalSpace X] {B : ℕ → Set X} (S : BinaryScheme X B)

theorem child_subset (l : List Bool) (b : Bool) : S.sets (b :: l) ⊆ S.sets l := by
  cases b
  · exact subset_union_left.trans (S.cover l).subset
  · exact subset_union_right.trans (S.cover l).subset

/-- Select the unique child containing a given point of a cell. -/
def next (x : X) (l : List Bool) : Bool := by
  classical
  exact decide (x ∈ S.sets (true :: l))

def addressPrefix (x : X) (n : ℕ) : List Bool :=
  Nat.rec [] (fun _ l => S.next x l :: l) n

/-- Binary address of a point in the full clopen scheme. -/
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

/-- A point in a cell has exactly that finite binary address. -/
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

/-- Each address coordinate is locally constant on an open cell. -/
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

/-- Every binary branch is realized, by compactness of nested closed cells. -/
theorem surjective_code [CompactSpace X] : Surjective S.code := by
  intro z
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => S.sets (PiNat.res z n))
    (fun n => by simpa only [PiNat.res_succ] using S.child_subset (PiNat.res z n) (z n))
    (fun n => S.nonempty _) ((S.clopen _).isClosed.isCompact) (fun n => (S.clopen _).isClosed)
  refine ⟨x, funext fun n => ?_⟩
  have he : PiNat.res (S.code x) (n + 1) = PiNat.res z (n + 1) := by
    simpa only [PiNat.res_length] using S.res_code_of_mem _ (mem_iInter.mp hx (n + 1))
  exact PiNat.res_eq_res.mp he (Nat.lt_succ_self n)

/-- Equal addresses force equal membership in every enumerated basis element. -/
theorem basis_mem_iff_of_code_eq {x y : X} (he : S.code x = S.code y) (n : ℕ) :
    x ∈ B n ↔ y ∈ B n := by
  have hx := S.code_mem x (n + 1)
  have hy := S.code_mem y (n + 1)
  rw [← he] at hy
  have hd : S.sets (PiNat.res (S.code x) (n + 1)) ⊆ B n ∨
      S.sets (PiNat.res (S.code x) (n + 1)) ⊆ (B n)ᶜ := by
    simpa only [PiNat.res_succ, PiNat.res_length] using
      S.decides (PiNat.res (S.code x) n) (S.code x n)
  rcases hd with hd | hd
  · exact ⟨fun _ => hd hy, fun _ => hd hx⟩
  · exact ⟨fun h => False.elim (hd hx h), fun h => False.elim (hd hy h)⟩

/-- A deciding basis separates points, so the address map is injective. -/
theorem injective_code [T2Space X] (hB : IsTopologicalBasis (range B)) : Injective S.code := by
  intro x y he
  by_contra hxy
  obtain ⟨U, ⟨n, rfl⟩, hxU, hsub⟩ := hB.exists_subset_of_mem_open
    (show x ∈ ({y} : Set X)ᶜ from hxy) isOpen_compl_singleton
  have hyU := (S.basis_mem_iff_of_code_eq he n).mp hxU
  exact hsub hyU rfl

include S in
/-- The full binary coding is a homeomorphism by compactness and Hausdorffness. -/
theorem nonempty_homeomorph [CompactSpace X] [T2Space X]
    (hB : IsTopologicalBasis (range B)) : Nonempty (X ≃ₜ (ℕ → Bool)) := by
  let e : X ≃ (ℕ → Bool) := Equiv.ofBijective S.code ⟨S.injective_code hB, S.surjective_code⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) S.continuous_code⟩

end BinaryScheme

/-- A second-countable clopen basis admits an enumeration which remains a basis. -/
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

/-- Brouwer's characterization, sufficient core in its compact Hausdorff
second-countable form. All binary branches, not just a Cantor subset, are realized. -/
theorem nonempty_homeomorph_of_secondCountable (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [SecondCountableTopology X] [PerfectSpace X]
    [Nonempty X] (hB : HasClopenBasis X) : Nonempty (X ≃ₜ (ℕ → Bool)) := by
  obtain ⟨B, hcl, hb⟩ := exists_countable_clopen_basis X hB
  obtain ⟨S⟩ := exists_binary_scheme hB B hcl
  exact S.nonempty_homeomorph hb

/-- Cantor space has a clopen cylinder basis. The proof follows the earlier
Baire-space package, using the upstream finite-prefix basis for Bool coordinates. -/
theorem isClopen_cylinder (x : ℕ → Bool) (n : ℕ) : IsClopen (PiNat.cylinder x n) := by
  refine ⟨?_, PiNat.isOpen_cylinder _ x n⟩
  change IsClosed {y : ℕ → Bool | ∀ i, i < n → y i = x i}
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

/-- Cantor space has a basis of clopen sets. -/
theorem cantor_hasClopenBasis : HasClopenBasis (ℕ → Bool) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.isOpen
  · intro x U hx hU
    obtain ⟨V, ⟨y, n, rfl⟩, hxV, hVU⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ => Bool)).exists_subset_of_mem_open hx hU
    exact ⟨PiNat.cylinder y n, isClopen_cylinder y n, hxV, hVU⟩

/-- Changing the next coordinate supplies another point in every cylinder. -/
theorem cantor_perfectSpace : PerfectSpace (ℕ → Bool) := by
  constructor
  rw [preperfect_iff_nhds]
  intro x _ U hU
  obtain ⟨V, ⟨y, n, rfl⟩, hxV, hVU⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => Bool)).mem_nhds_iff.mp hU
  let z := Function.update x n (!(x n))
  have hz : z ∈ PiNat.cylinder y n := by
    intro k hk
    change Function.update x n (!(x n)) k = y k
    rw [Function.update_of_ne (by omega : k ≠ n)]
    exact hxV k hk
  refine ⟨z, ⟨hVU hz, mem_univ _⟩, ?_⟩
  intro he
  have hn := congrFun he n
  cases h : x n <;> simp [z, h] at hn

/-- Clopen-basis pullback, adapted from the prior Baire-space characterization. -/
theorem HasClopenBasis.of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (hB : HasClopenBasis Y) (e : X ≃ₜ Y) : HasClopenBasis X := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.isOpen
  · intro x U hx hU
    obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_subset_of_mem_open
      (mem_image_of_mem e hx) (e.isOpenMap U hU)
    refine ⟨e ⁻¹' V, hV.preimage e.continuous, hxV, ?_⟩
    intro z hz
    obtain ⟨w, hw, he⟩ := hVU hz
    exact e.injective he ▸ hw

/-- Absence of isolated points is preserved under homeomorphism. -/
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

/-- Brouwer's sufficient direction in the standard compact-metrizable form. -/
theorem nonempty_homeomorph (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [MetrizableSpace X] [PerfectSpace X] [Nonempty X] (hB : HasClopenBasis X) :
    Nonempty (X ≃ₜ (ℕ → Bool)) :=
  nonempty_homeomorph_of_secondCountable X hB

/-- Full intrinsic characterization: nonempty, compact, metrizable,
zero-dimensional, and without isolated points. None of these is tacit. -/
theorem nonempty_homeomorph_iff (X : Type*) [TopologicalSpace X] :
    Nonempty (X ≃ₜ (ℕ → Bool)) ↔ Nonempty X ∧ CompactSpace X ∧ MetrizableSpace X ∧
      HasClopenBasis X ∧ PerfectSpace X := by
  constructor
  · rintro ⟨e⟩
    let := cantor_perfectSpace
    exact ⟨e.toEquiv.nonempty, e.symm.compactSpace, e.isEmbedding.metrizableSpace,
      cantor_hasClopenBasis.of_homeomorph e, perfectSpace_of_homeomorph e⟩
  · rintro ⟨hne, hc, hm, hb, hp⟩
    let := hne
    let := hc
    let := hm
    let := hp
    exact nonempty_homeomorph X hb

end CantorCharacterization
