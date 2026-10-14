# Definition correspondence

`Smirnov.LocallyMetrizable X` means exactly
`∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U`.
The topology on `U` is the inherited subtype topology. The expanded criterion
exposes this formula directly. It requires an actual open neighborhood, and
puts no restriction on the patch's cardinality or density.

The reused `NagataSmirnov.HasSigmaLocallyFiniteBasis X` means
`∃ B : ℕ → Set (Set X), (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
IsTopologicalBasis (⋃ n, B n)`.
Only the layer index is countable; individual layers may be uncountable.
It is defined in the credited vendored registered support and explicitly included in
the independently checkable Challenge. Its reuse is credited, not claimed anew.

`Smirnov.compatibleMetric h` extracts a metric after the proof establishes
metrizability. The metric's induced topology equals the original topology,
certified by `compatibleMetric_topology`. It introduces no additional assumption.
Mathlib's `ParacompactSpace` excludes separation, hence `T2Space` appears
explicitly in the complete criterion.
