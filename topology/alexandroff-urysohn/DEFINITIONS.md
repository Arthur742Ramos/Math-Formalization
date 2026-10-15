# Definitions and statement contracts

All four definitions are exposed public definitions in the canonical Challenge
and in the reusable module. Their literal values are selected for comparison.

| Name | Exact mathematical meaning |
| --- | --- |
| `pointStar C x` | `{y | ∃ U ∈ C, x ∈ U ∧ y ∈ U}`, the union of cover members containing `x`. |
| `IsOpenCover C` | Every member of `C` is open, and every point belongs to a member. |
| `IsMetrizingSequence C` | Each `C n` is an open cover; intersecting `U,V ∈ C (n+1)` have `U ∪ V ⊆ W` for some `W ∈ C n`; for every open neighborhood `O` of `x`, some `pointStar (C n) x` is contained in `O`. |
| `coverRelation C` | `{p | p.2 ∈ pointStar C p.1}`, literally pairs sharing one member. |

`IsMetrizingSequence.nhds_basis` proves that the cofinal stars really form a
neighborhood basis. No metric, uniformity, local finiteness, separation or
countability of a cover is encoded in these definitions. The countable index
is only the sequence index `ℕ`.

The selected `exists_uniformity` theorem concludes an actual uniform structure,
equality with the original topology, and the precise co-membership entourage
basis. `pseudoMetrizable_iff` has no separation premise. `metrizable_iff` adds
`T0Space X`, without which an indiscrete two-point space is a counterexample.
`exists_compatibleMetric` returns an actual `MetricSpace X` with exactly the
original induced topology. No nonempty-space premise is used.

The definitions use standard `Set`, `IsOpen`, and filter-basis concepts from
Mathlib. Empty covers are allowed exactly when the space is empty. Cover
members need not be nonempty individually, countable, or locally finite.
