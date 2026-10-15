/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.LocallyFinite

/- Reused from registered PALOMAR-2026-10-14-000001, source commit
6aa68b2cb67719a187e64de29567443575eb560e, topology/nagata-smirnov/SigmaBasis.lean.
Only module import paths are adapted to this vendored support directory.
No new Nagata–Smirnov claim is made by this project. -/

/-!
# Sigma locally finite bases and open exhaustion

The layers of a sigma locally finite basis can have arbitrary cardinality.
Regularity supplies a countable open cover with closures contained in
each prescribed open set. This proves perfect normality without any
second-countability or separability assumption.

Reference: K. Sakai, *Geometric Aspects of General Topology*, second-edition
author manuscript (November 2, 2023), chapter 2, Lemma 2.3.3.
-/

@[expose] public section

open Set TopologicalSpace Topology

namespace NagataSmirnov

variable {X : Type*} [TopologicalSpace X]

/-- An open basis expressed as countably many locally finite families.
No individual family is required to be countable. -/
def HasSigmaLocallyFiniteBasis (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ B : ℕ → Set (Set X),
    (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
      IsTopologicalBasis (⋃ n, B n)

/-- The union of all members of one basis layer whose closures lie in `U`. -/
def basisShrinkLayer (B : ℕ → Set (Set X)) (U : Set X) (n : ℕ) : Set X :=
  ⋃ V : {V : B n // closure (V : Set X) ⊆ U}, (V.1 : Set X)

theorem basisShrinkLayer_isOpen {B : ℕ → Set (Set X)}
    (hB : IsTopologicalBasis (⋃ n, B n)) (U : Set X) (n : ℕ) :
    IsOpen (basisShrinkLayer B U n) := by
  exact isOpen_iUnion fun V => hB.isOpen (mem_iUnion_of_mem n V.1.2)

theorem closure_basisShrinkLayer_subset {B : ℕ → Set (Set X)}
    (hB : ∀ n, LocallyFinite (fun V : B n => (V : Set X))) (U : Set X) (n : ℕ) :
    closure (basisShrinkLayer B U n) ⊆ U := by
  have hfin : LocallyFinite
      (fun V : {V : B n // closure (V : Set X) ⊆ U} => (V.1 : Set X)) :=
    (hB n).comp_injective Subtype.val_injective
  rw [basisShrinkLayer, hfin.closure_iUnion]
  exact iUnion_subset fun V => V.2

theorem iUnion_basisShrinkLayer_eq [RegularSpace X] {B : ℕ → Set (Set X)}
    (hB : IsTopologicalBasis (⋃ n, B n)) {U : Set X} (hU : IsOpen U) :
    (⋃ n, basisShrinkLayer B U n) = U := by
  apply Subset.antisymm
  · refine iUnion_subset fun n => iUnion_subset fun V => ?_
    exact subset_closure.trans V.2
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_closure_subset (hU.mem_nhds hx)
    obtain ⟨n, hVn⟩ := mem_iUnion.mp hV
    exact mem_iUnion_of_mem n (mem_iUnion_of_mem ⟨⟨V, hVn⟩, hVU⟩ hxV)

/-- Every open set admits a countable open cover whose closures stay inside it.
The cover is not asserted to be increasing. -/
theorem HasSigmaLocallyFiniteBasis.exists_open_exhaustion [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) {U : Set X} (hU : IsOpen U) :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧
      (∀ n, closure (V n) ⊆ U) ∧ (⋃ n, V n) = U := by
  obtain ⟨B, hfin, hB⟩ := h
  exact ⟨basisShrinkLayer B U, basisShrinkLayer_isOpen hB U,
    closure_basisShrinkLayer_subset hfin U, iUnion_basisShrinkLayer_eq hB hU⟩

theorem HasSigmaLocallyFiniteBasis.hasSeparatingCover [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) {s t : Set X}
    (ht : IsClosed t) (hst : Disjoint s t) : HasSeparatingCover s t := by
  obtain ⟨V, hVo, hVsub, hVcov⟩ := h.exists_open_exhaustion ht.isOpen_compl
  refine ⟨V, ?_, fun n => ⟨hVo n, ?_⟩⟩
  · rw [hVcov]
    exact hst.subset_compl_right
  · exact disjoint_compl_left.mono_left (hVsub n)

/-- A regular space with a sigma locally finite basis is normal. -/
theorem HasSigmaLocallyFiniteBasis.normalSpace [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) : NormalSpace X where
  normal _s _t hs ht hst := hasSeparatingCovers_iff_separatedNhds.mp
    ⟨h.hasSeparatingCover ht hst, h.hasSeparatingCover hs hst.symm⟩

/-- A regular space with a sigma locally finite basis is perfectly normal. -/
theorem HasSigmaLocallyFiniteBasis.perfectlyNormalSpace [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) : PerfectlyNormalSpace X where
  toNormalSpace := h.normalSpace
  closed_gdelta s hs := by
    obtain ⟨V, -, hVsub, hVcov⟩ := h.exists_open_exhaustion hs.isOpen_compl
    have hcl : (⋃ n, closure (V n)) = sᶜ := by
      apply Subset.antisymm
      · exact iUnion_subset hVsub
      · rw [← hVcov]
        exact iUnion_mono fun n => subset_closure
    have heq : s = ⋂ n, (closure (V n))ᶜ := by
      rw [← compl_iUnion, hcl, compl_compl]
    rw [heq]
    exact IsGδ.iInter_of_isOpen fun n => isClosed_closure.isOpen_compl

end NagataSmirnov
