/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Substantive proof and packaging contributions: OpenAI Codex.
-/
module

public import Mathlib.Topology.Compactness.CountablyCompact
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact closures in countable-support products

The product topology and its canonical subtype topology are used throughout.
The omega-bounded theorem assumes T1 factors, not first countability or
compactness. The compactness criterion assumes compact Hausdorff factors.
-/

public section

open Set Filter Topology Function

universe u v w

namespace SigmaCompact

/-- Every countable subset has compact closure. -/
@[expose] def OmegaBounded (Y : Type w) [TopologicalSpace Y] : Prop :=
  ∀ s : Set Y, s.Countable → IsCompact (closure s)

variable {ι : Type u} {X : ι → Type v}

/-- Coordinates at which a point differs from the explicit basepoint. -/
@[expose] def deviationSupport (b x : ∀ i, X i) : Set ι := {i | x i ≠ b i}

/-- Countable, rather than finite, support; topology is the product subspace topology. -/
abbrev SigmaProduct (b : ∀ i, X i) :=
  {x : ∀ i, X i // (deviationSupport b x).Countable}

/-- Factors with at least one value distinct from the supplied basepoint. -/
@[expose] def activeCoordinates (b : ∀ i, X i) : Set ι :=
  {i | ∃ x : X i, x ≠ b i}

variable [∀ i, TopologicalSpace (X i)]

/-- A countable set of Sigma-points is contained, together with its ambient
closure, in a closed compact box using only countably many coordinates.
This is the coordinate-closure construction of Gutik--Ravsky Prop. 2.4,
specialized to omega-bounded factors. -/
theorem exists_compact_trap (b : ∀ i, X i) [∀ i, T1Space (X i)]
    (hX : ∀ i, OmegaBounded (X i)) {s : Set (∀ i, X i)}
    (hs : s.Countable) (hsupp : ∀ x ∈ s, (deviationSupport b x).Countable) :
    ∃ (J : Set ι) (K : Set (∀ i, X i)), J.Countable ∧ IsClosed K ∧ IsCompact K ∧
      closure s ⊆ K ∧ ∀ x ∈ K, deviationSupport b x ⊆ J := by
  classical
  let J : Set ι := ⋃ x ∈ s, deviationSupport b x
  let K : Set (∀ i, X i) := {x | ∀ i, x i ∈ closure (eval i '' s)}
  have hKclosed : IsClosed K := by
    convert isClosed_iInter (fun i => (isClosed_closure :
      IsClosed (closure (eval i '' s))).preimage (continuous_apply i)) using 1
    ext x
    simp only [K, mem_ofPred_eq, mem_iInter, mem_preimage]
  refine ⟨J, K, hs.biUnion hsupp, hKclosed,
    isCompact_pi_infinite (fun i => hX i _ (hs.image _)),
    closure_minimal (fun x hx i => subset_closure (mem_image_of_mem _ hx)) hKclosed, ?_⟩
  intro x hx i hi
  by_contra hij
  have hconst : eval i '' s ⊆ {b i} := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hne
    exact hij (mem_iUnion_of_mem y (mem_iUnion_of_mem hy hne))
  exact hi (closure_minimal hconst isClosed_singleton (hx i))

/-- Sigma-products of T1 omega-bounded factors are omega-bounded.
No countability of the index or first countability of the factors is assumed. -/
theorem omegaBounded_sigmaProduct (b : ∀ i, X i) [∀ i, T1Space (X i)]
    (hX : ∀ i, OmegaBounded (X i)) : OmegaBounded (SigmaProduct b) := by
  intro s hs
  obtain ⟨J, K, hJ, _, hK, hcl, hsub⟩ := exists_compact_trap b hX
    (hs.image Subtype.val) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  have hc : IsCompact (closure (Subtype.val '' s)) :=
    hK.of_isClosed_subset isClosed_closure hcl
  have hrange : closure (Subtype.val '' s) ⊆ range (Subtype.val : SigmaProduct b → _) := by
    intro x hx
    exact ⟨⟨x, hJ.mono (hsub x (hcl hx))⟩, rfl⟩
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc hrange

/-- Omega-boundedness implies canonical Mathlib countable compactness. -/
theorem countablyCompactSpace_of_omegaBounded {Y : Type w} [TopologicalSpace Y]
    (hY : OmegaBounded Y) : CountablyCompactSpace Y := by
  constructor
  apply IsCountablyCompact.of_seq_clusterPt
  intro a _
  obtain ⟨y, _, hy⟩ := (hY (range a) (countable_range a)).isCountablyCompact.seq_clusterPt a
    (Eventually.of_forall fun n => subset_closure (mem_range_self n))
  exact ⟨y, mem_univ _, hy⟩

/-- The countably compact Sigma-product theorem for arbitrary T1 omega-bounded factors. -/
theorem countablyCompactSpace_sigmaProduct (b : ∀ i, X i) [∀ i, T1Space (X i)]
    (hX : ∀ i, OmegaBounded (X i)) : CountablyCompactSpace (SigmaProduct b) :=
  countablyCompactSpace_of_omegaBounded (omegaBounded_sigmaProduct b hX)

/-- Compact T1 factors provide a useful specialization, without any metrizability premise. -/
theorem omegaBounded_sigmaProduct_of_compact (b : ∀ i, X i)
    [∀ i, T1Space (X i)] [∀ i, CompactSpace (X i)] : OmegaBounded (SigmaProduct b) :=
  omegaBounded_sigmaProduct b (fun _ _ _ => isClosed_closure.isCompact)

/-- Finite-coordinate replacement proves density, for the ordinary product topology.
This supporting argument also appears in the earlier SigmaFrechet package. -/
theorem dense_sigmaProduct (b : ∀ i, X i) :
    Dense {x : ∀ i, X i | (deviationSupport b x).Countable} := by
  classical
  apply dense_iff_inter_open.mpr
  intro o ho hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, U, hU, hs⟩ := isOpen_pi_iff.mp ho x hx
  let y : ∀ i, X i := fun i => if i ∈ s then x i else b i
  refine ⟨y, hs ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ s := hi
    simpa [y, hi'] using (hU i hi').2
  · apply s.finite_toSet.countable.mono
    intro i hi
    by_contra his
    have his' : i ∉ s := his
    exact hi (by simp [y, his'])

/-- Sharp compactness criterion. Degenerate factors do not count: arbitrarily
many singleton factors are allowed. The basepoint also covers the empty index. -/
theorem compactSpace_sigmaProduct_iff (b : ∀ i, X i)
    [∀ i, T2Space (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace (SigmaProduct b) ↔ (activeCoordinates b).Countable := by
  classical
  constructor
  · intro h
    let := h
    have hc : IsCompact {x : ∀ i, X i | (deviationSupport b x).Countable} := by
      convert isCompact_univ.image
        (continuous_subtype_val : Continuous (Subtype.val : SigmaProduct b → _)) using 1
      ext x
      simp
    have hall : {x : ∀ i, X i | (deviationSupport b x).Countable} = univ := by
      rw [← hc.isClosed.closure_eq, (dense_sigmaProduct b).closure_eq]
    let x : ∀ i, X i := fun i => if h : ∃ a : X i, a ≠ b i then h.choose else b i
    have hx : (deviationSupport b x).Countable := by
      have : x ∈ {x : ∀ i, X i | (deviationSupport b x).Countable} := by rw [hall]; trivial
      exact this
    apply hx.mono
    intro i hi
    change ∃ a : X i, a ≠ b i at hi
    change x i ≠ b i
    simpa only [x, dite_eq_left hi] using hi.choose_spec
  · intro h
    apply (isCompact_iff_compactSpace (s := {x : ∀ i, X i | (deviationSupport b x).Countable})).mp
    have hall : {x : ∀ i, X i | (deviationSupport b x).Countable} = univ := by
      apply eq_univ_of_forall
      intro x
      change (deviationSupport b x).Countable
      apply h.mono
      intro i hi
      change ∃ a : X i, a ≠ b i
      exact ⟨x i, hi⟩
    rw [hall]
    exact isCompact_univ

/-- Every uncountable discrete Boolean Sigma-product is countably compact
but not compact. The countable-support restriction is essential. -/
theorem boolean_sigma_countablyCompact_not_compact (hι : ¬ Countable ι) :
    CountablyCompactSpace (SigmaProduct (X := fun _ : ι => Bool) (fun _ => false)) ∧
    ¬ CompactSpace (SigmaProduct (X := fun _ : ι => Bool) (fun _ => false)) := by
  constructor
  · exact countablyCompactSpace_of_omegaBounded (omegaBounded_sigmaProduct_of_compact _)
  · intro hc
    have h := (compactSpace_sigmaProduct_iff (X := fun _ : ι => Bool) (fun _ => false)).mp hc
    have heq : activeCoordinates (X := fun _ : ι => Bool) (fun _ => false) = univ := by
      ext i
      simp [activeCoordinates]
    rw [heq] at h
    exact hι (countable_univ_iff.mp h)

end SigmaCompact
