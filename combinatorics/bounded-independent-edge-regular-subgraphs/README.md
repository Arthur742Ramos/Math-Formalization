# Regular induced subgraphs in independent-edge arrays

Lean development for the paper *Regular induced subgraphs in bounded
independent-edge arrays* by Arthur Freitas Ramos, David Barros Hulak and
Ruy J. G. B. de Queiroz. The working source is the supplied manuscript
with PDF SHA-256
`7cba4a4dcf525926b283ca036f4970d6321f50dd2ca0f3efe01b643be4a1e32d`.

On a finite linearly ordered vertex type, `Edge` uses the increasing
orientation of each unordered pair. The model samples one coordinate per
pair from its Bernoulli law. `graphLaw_ae_binary` establishes support on
0–1 assignments, and `integral_degreeSum` identifies the expected degree
with the sum of the incident probabilities. The marginal
`measurePreserving_induce` shows that restricting the coordinates to a
vertex set gives the product law for its induced array.

## Source map

| Manuscript location | Lean declaration | Scope |
| --- | --- | --- |
| §8, p. 11, Proposition 8.1 | `probability_regular_degree_atom_le`, `probability_regular_le_variation_gaussian` | The prescribed common-degree and total regularity bounds. |
| §8, p. 11, upper tail | `probability_at_least_order_le_sum_pow`, `probability_at_least_order_le_geometric` | The sum over all larger orders and the geometric bound at the order-`n^(2/3)` scale. |
| §8, p. 12, upper conclusion of Theorem 8.2 | `probability_linear_product_exact_order_le`, `probability_linear_product_upper_tendsto_zero` | The weighted first-moment estimate and vanishing upper tail at the square-root scale for the specified rank-one model. |
| §9, p. 12, Proposition 9.1 | `probability_regular_le`, `probability_induced_regular_le` | The bound is `exp (-2 * V / (k - 2))` for every set of order `k ≥ 3`, including arrays with edge probabilities 0 or 1. |
| §9, p. 13, first displayed estimate | `probability_exact_order_le` | Union bound over the sets of cardinality exactly `k`. |
| §9, p. 13, necessary small variation at fixed order | `exists_small_variation_of_probability_exact_order_ge` | A probability of at least γ > 0 forces a k-set with the stated logarithmic variation bound. |
| §9, p. 13, remaining variation bounds | `probability_exact_order_le_of_large_variation`, `exists_small_variation_of_probability_at_least_order_ge` | The power-law probability bound and the necessary variation bound across all larger orders. |
| §9, p. 13, union over larger orders | `probability_at_least_order_le` | Union bound over every set of cardinality at least `k`, with its own cardinality in the exponent. |
| §1, pp. 1–2, Theorem 1.1(1)–(4) | `Theorem1_1_arbitrary`, `Theorem1_1_equalDegrees`, `Theorem1_1_lipschitz`, `Theorem1_1_lowRank` | Statement definitions. Their proofs remain open in this development. |

The `V = 0` case uses the probability bound by one. For positive `V`,
the proof applies Hoeffding's inequality to the sum with one summand
per edge. On a regular outcome that sum is exactly `V`, independently of
the common degree. The proof establishes the coefficient identity
`∑_{i<j} (vᵢ + vⱼ)² = (k - 2) ∑ᵢ vᵢ²` for a centred vertex vector.

Mathlib's binomial random graph uses a single common edge probability.
Here the proof uses a product law with a separate parameter for every
edge and Mathlib's sub-Gaussian bounds for independent random variables.
The development does not use the binomial random graph definition.
[Binomial random graphs at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean)
and [Mathlib's Hoeffding lemmas](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Probability/Moments/SubGaussian.lean).

## Palomar scope

The prospective research result is Theorem 1.1. Its exact-order bounds
concern probabilistic combinatorics and extend the setting of the
homogeneous random-graph result of Krivelevich, Sudakov and Wormald.
Proposition 9.1 and its union bounds form a supporting development.
[Regular induced subgraphs of a random graph](https://arxiv.org/abs/0808.2023).

The finite analytic setup includes the exact vertex-tilt likelihood, the
quadratic cost of its inverse change of measure and the Fourier modulus
bound. Exact degree-vector inversion applies to the full array and to the
array with the overlap clique's edges removed. The latter has explicit
quadratic, inverse-entry, row-sum and determinant comparison bounds. The
even degree lattice gives the simultaneous π shift used in the centred
atom proof. Induced arrays are independent when their vertex sets overlap
in at most one vertex.

The remaining proof work includes the centred degree atom (Theorem B.2),
the atom with overlap edges deleted (Proposition C.1), and their use in the
overlap second moment. The variance extraction and block arguments then
supply the lower bounds in Theorem 1.1. The [coverage map](COVERAGE.md)
records the remaining work for each source result.

This is a development package. Challenge and Solution selection depends on
which research conclusions have complete proofs. Independent mathematical
review and Palomar verification are pending.

## Local checks

Run from this directory with the pinned Lean toolchain and Lake manifest.

```powershell
lake exe cache get
lake build
lake env lean Audit.lean
```
