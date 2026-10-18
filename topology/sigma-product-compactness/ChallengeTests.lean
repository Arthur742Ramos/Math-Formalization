module

import SigmaCompactChallenge

open Set Filter Topology Function SigmaCompact

universe u v w
variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

example (b : ∀ i, X i) [∀ i, T1Space (X i)] (hX : ∀ i, OmegaBounded (X i))
    {s : Set (∀ i, X i)} (hs : s.Countable)
    (hp : ∀ x ∈ s, (deviationSupport b x).Countable) :
    ∃ (J : Set ι) (K : Set (∀ i, X i)), J.Countable ∧ IsClosed K ∧ IsCompact K ∧
      closure s ⊆ K ∧ ∀ x ∈ K, deviationSupport b x ⊆ J :=
  SigmaCompact.exists_compact_trap b hX hs hp

example (b : ∀ i, X i) [∀ i, T1Space (X i)] (hX : ∀ i, OmegaBounded (X i)) :
    OmegaBounded (SigmaProduct b) := SigmaCompact.omegaBounded_sigmaProduct b hX

example (b : ∀ i, X i) [∀ i, T1Space (X i)] (hX : ∀ i, OmegaBounded (X i)) :
    CountablyCompactSpace (SigmaProduct b) :=
  SigmaCompact.countablyCompactSpace_sigmaProduct b hX

example (b : ∀ i, X i) [∀ i, T1Space (X i)] [∀ i, CompactSpace (X i)] :
    OmegaBounded (SigmaProduct b) := SigmaCompact.omegaBounded_sigmaProduct_of_compact b

example (b : ∀ i, X i) [∀ i, T2Space (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace (SigmaProduct b) ↔ (activeCoordinates b).Countable :=
  SigmaCompact.compactSpace_sigmaProduct_iff b

example (hι : ¬ Countable ι) :
    CountablyCompactSpace (SigmaProduct (X := fun _ : ι => Bool) (fun _ => false)) ∧
    ¬ CompactSpace (SigmaProduct (X := fun _ : ι => Bool) (fun _ => false)) :=
  SigmaCompact.boolean_sigma_countablyCompact_not_compact hι

example {Y : Type w} [TopologicalSpace Y] :
    SigmaCompact.OmegaBounded Y ↔ ∀ s : Set Y, s.Countable → IsCompact (closure s) := Iff.rfl

example (b x : ∀ i, X i) : SigmaCompact.deviationSupport b x = {i | x i ≠ b i} := rfl

example (b : ∀ i, X i) : SigmaCompact.activeCoordinates b = {i | ∃ x : X i, x ≠ b i} := rfl
