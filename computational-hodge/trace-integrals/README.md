# Ordinary integrals of raw computational circle paths

For a continuous real coefficient on the unit circle, this project proves
that its ordinary integral along every actual finite based computational
circle trace equals the signed period of a proved harmonic cochain. The trace
may contain arbitrary nested concatenations, reversals and reflexive paths.
Corners remain in the path; no smooth representative replaces it.

## Actual analytic construction

The user's `GeometricTrace` retains endpoint indices and actual binary path
concatenation/reversal. Its `realize` function executes those constructors as
actual continuous paths. The primitive is the actual once-around circle path.
`actualLift p` is the ordinary covering lift of that realized path beginning
at zero, extended to the real parameter line using interval projection.

The definition of `rawIntegral α p` is the ordinary Bochner interval integral
over `[0,1]` of `α(realize p(t)) * deriv(actualLift p)(t)`. It is not a sum of
edge periods. A clamped recursive real-lift construction follows the actual
half-interval concatenation and reversal formulas. Projection, initial value,
continuous clamped tails and covering uniqueness identify it globally with
the actual lift. The construction is proved globally Lipschitz and
differentiable outside a constructed finite corner set. No separate formal
piecewise-affine predicate is asserted.

Integrability is proved independently: the actual circle coefficient is bounded
by compactness, the derivative is measurable, and the proved Lipschitz bound
bounds its norm, including totalized corner values. The composed ordinary
primitive is continuous and has the required derivative off the finite set.
Pinned Mathlib's FTC off a countable exceptional set therefore applies. Finite
exceptional differentiability alone is never used to infer integrability.

Writing `m = ∫₀¹ α([x]) dx`, the resulting formula is

```text
rawIntegral α p = m * (signed count of p) = period p (meanHarmonic α).
```

The signed count is derived from syntax and proved equal to actual winding;
it enters only after the analytic proof. Actual integrals add under the
actual concatenation, negate under reversal, are invariant under homotopy of
the actual realizations, and satisfy nested associativity and cancellation.
All raw integrals vanish exactly when the mean vanishes. The unit trace makes
this detection and the harmonic-cochain uniqueness theorem nonvacuous.

`meanHarmonic` belongs to the existing actual finite Euclidean subspace
`Closed ∩ Exactᗮ`. Its Unit coefficient is the same mean value used by PR65,
constructed directly here rather than identified literally with that package's
named rooted reconstruction. Closedness covers all actual geometric relation
cells, including inactive nonzero endpoints; finite `Exact` is proved zero.
Analytic exactness is a distinct notion developed in the predecessor.

## Scope and attribution

This extends the raw-corner limitation of
[PR65's flat-circle result](https://github.com/Arthur742Ramos/Math-Formalization/tree/4c48f1cd68bed76d69051bdc3a706327f2d2fe27/computational-hodge/circle-hodge).
That project proves the coefficient/potential Hodge decomposition and integration
on C1 representatives. Here ordinary integration is proved on the actual raw
finite trace, with a compositional analytic semantics. The audience is verified
computational-path semantics and formalized nonsmooth integration. Classical
calculus and circle topology are credited infrastructure; novelty or editorial
acceptance is not promised.

The path model is attributed to the user's
[computational-path paper](https://arxiv.org/abs/2608.04228v3) and pinned
TopologicalComputationalPaths source. Its four paper authors are distinct
from the project's recorded authors and maintainers. Classical period/discrete
context is credited to [Hatcher](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)
and [Jiang–Lim–Yao–Ye](https://arxiv.org/abs/0811.1067v2). Source mappings and
MIT/Apache-2.0 attributions retain complete used declarations and proofs.

Coefficients are actual continuous real functions on the flat one-dimensional
circle, and traces are finite words in the specified actual unit-winding
primitive. Arbitrary continuous or nonrectifiable paths, infinite computations,
arbitrary reparameterization, manifold differential-form/de Rham comparison,
higher-dimensional/Kähler Hodge, Laplacians and numerical algorithms are outside
this formalization. Classical covering choices remain noncomputable.

## Source and validation

Lean `4.35.0-rc2`, compiler `11acb17ec6b07a8f9e9173e6845197929540936b`,
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned. Nine ordered
mathematical modules retain every proof. `make_surface.py` removes only
module/import/visibility directives to generate the complete Challenge and
Solution surfaces. They share one implementation, not independent proofs.
The unchanged renderer displays selected declarations; complete dependency
source remains in the public source and static artifact.

The comparator selects 42 theorems and 28 definitions, with literal value,
kind, kernel-defeq and closure comparisons, random aliases and four negative
controls. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Native validation also runs a supplemental unchanged comparator pass that
compares complete selected-definition value dependencies without definition
holes, including in the random-alias check. Selected theorem proofs retain
the comparator's normal freedom. This does not modify the protected canonical
verifier.
Material dependency predicates and critical theorem contracts have exact pinned
source evidence and separate Challenge/Solution semantic audits.

All necessary validation runs locally under root AGENTS.md. Package commands
are `lake build`, `python3 scripts/check_package.py --upstream-root PATH`, and
`python3 scripts/check_interfaces.py`; root catalog, original exact-commit
canonical full/render, kernel, browser, packet and independent-review checks
remain separate gates. Outcomes are recorded in source-bound external receipts,
without claiming release or registry acceptance from this source document.
