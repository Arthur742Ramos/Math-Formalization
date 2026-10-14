# The full Nagata–Smirnov metrization theorem

For a regular Hausdorff space, metrizability is equivalent to having an open
basis that is a countable union of locally finite families. Each layer may be
uncountable. No separability, second countability, local compactness or
nonemptiness assumption is imposed.

`NagataSmirnov.metrizable_iff_sigmaLocallyFiniteBasis` expands the basis
condition explicitly. `nagata_smirnov` packages it as
`HasSigmaLocallyFiniteBasis`. `compatible_metric_iff` states the same criterion
using existence of an actual `MetricSpace` whose topology equals the supplied
topology. `compatibleMetric` constructs that metric.

Mathlib's `T3Space` means regular plus T0 and entails Hausdorff separation.
Conversely a regular Hausdorff space has this class. Regularity alone suffices
for the intermediate perfect-normality theorem, without a separation axiom.

`SigmaBasis` proves closure-contained countable open covers and perfect
normality. `MetricBasis` uses existing metric paracompactness to refine ball
covers. `CompatibleMetric` proves uniform-metric continuity for arbitrary
locally finite supported coordinate families. `Metrization` constructs an
inducing map to a countable product of bounded-function metric spaces.
Only the product's layer index is countable.

The source is Katsuro Sakai, *Geometric Aspects of General Topology*, second
edition author manuscript dated November 2, 2023, chapter 2, Theorem 2.3.4(a),(c)
and Lemma 2.3.3, printed pp.43–44. The uploaded manuscript is available through
[the author’s ResearchGate upload](https://www.researchgate.net/publication/299698540_Metrization_and_Paracompact_Spaces).
The source's ℓ¹ embedding is replaced by a uniform-metric bounded-function
embedding, with local finiteness supplying the necessary continuity proof.
The sigma-discrete Bing equivalence is outside this package's scope.

Lean is pinned to `v4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Run `lake build` here.
`Challenge.lean` has complete proofs and imports only canonical Mathlib.
`Solution.lean` exports the reusable implementation modules.
`SemanticTests` checks empty and unrestricted discrete spaces and exact metric
topology compatibility. `AxiomAudit` checks every new public declaration.

Project authors:
- Arthur Freitas Ramos
- David Barros Hulak
- Ruy Jose Guerra Barretto de Queiroz

Responsible maintainers:
- Arthur Freitas Ramos
- David Barros Hulak
- Ruy Jose Guerra Barretto de Queiroz

OpenAI Codex authored substantial proofs, tests and packaging under Arthur's
authorization. Independent internal AI mathematical and implementation reviews
are documented in `REVIEW.md`. No human review, first-formalization priority,
Palomar submission or registration is asserted by this README.
