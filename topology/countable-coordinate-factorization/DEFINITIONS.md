# Exact selected declarations

All names are in namespace `CountableCoordinates`; all input/index/output
universes are independent. `s.domRestrict` is the ordinary coordinate projection.
The compact product uses the ordinary dependent product topology.

| Declaration | Exact assumptions and conclusion |
| --- | --- |
| `finite_coordinates_of_entourage` | Uniform factors, no compactness or nonemptiness: a product entourage contains all pairs agreeing on some finite coordinate set. |
| `countable_coordinates_of_uniformContinuous` | Uniform factors; T0 uniform target with countably generated uniformity; uniformly continuous map: a countable determining set. No basepoint or compactness. |
| `countable_coordinates_of_continuous` | Compact Hausdorff factors, metrizable target, continuous map: countable determining set. Empty factors allowed. |
| `refill` (definition) | Explicit full-product basepoint `a`, set `s`, subproduct point `z`: at i use z(i) if i∈s and a(i) otherwise. Classical membership choice is explicit in its implementation. |
| `restrict_refill` | Basepoint and arbitrary set: projection after refill is identity. |
| `uniformContinuous_refill` | Uniform factors, basepoint, arbitrary set: uniformly continuous section. |
| `exists_countable_uniform_factorization` | Uniform factors, T0 countably generated uniform target, explicit basepoint and uniform continuity: countable set, globally defined uniformly continuous factor, exact function equality. |
| `exists_countable_continuous_factorization` | Nonempty compact Hausdorff factors and metrizable target: countable set, globally defined continuous factor and exact function equality. |
| `factor_unique` | Fixed set and explicit full-product basepoint: equal composites imply equal factor functions. No continuity required. The support is not claimed unique or minimal. |
| `exists_common_countable_factorization` | Countable family of possibly different metrizable targets, nonempty compact Hausdorff factors: one countable coordinate set and continuous factors for every map. Empty family allowed. |
| `nontrivial_subset_of_injective` | Purely set theoretic, basepoint and injective map with determining set: all nontrivial factor indices belong to that set. |
| `countable_nontrivial_of_continuous_injective` | Nonempty compact Hausdorff factors, metrizable target, continuous injection: nontrivial factor indices countable. |
| `continuous_refill` | Arbitrary topological factors, basepoint and set: continuous refill section. |
| `compact_product_metrizable_iff` | Nonempty compact Hausdorff factors: product metrizable iff every factor metrizable and indices of nontrivial factors countable. Singleton factors can have arbitrary cardinality. |

The auxiliary `metrizable_countable_product` packages canonical Mathlib
countably generated uniformity infrastructure and is not separately selected
as a substantive result. Selected theorems using it still receive transitive
audit. All selected declarations elaborate in Challenge independently of
Solution. Both use the same full proved sources; Challenge has no project-local
imports. No undefined Challenge surrogate is introduced.
