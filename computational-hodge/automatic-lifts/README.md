# Automatic AC circle lifts and computational harmonic periods

This package removes the supplied-real-lift premise from the unit-circle bridge.
An `AmbientLoop` is an arbitrary function `R -> C` that is absolutely continuous
on `[0,1]`, has complex norm one there, and starts and ends at one. No regularity
or unit-norm condition is imposed outside the interval. No real lift, global
Lipschitz bound, finite-energy premise or computational representative is input.

The actual circle homeomorphism and topological covering construct a zero-based
real lift, extended by canonical interval clamping. Its absolute continuity is
proved: the complex chord formula and Jordan's inequality give
`4*|s-t| <= |exp(2*pi*i*s)-exp(2*pi*i*t)|` when `|s-t| <= 1/2`.
Compact uniform continuity of the constructed real lift controls each small
interval. Summing the resulting inverse estimates over finite disjoint intervals
transfers absolute continuity from the original complex curve. This supplies the
analytic regularity that a topological path-lifting theorem alone does not give.

`canonical_curve` proves actual realization of the clamped input. The lift starts
at zero, has integral endpoint and is unique on `[0,1]` among admitted zero-based
AC lifts realizing the input. Conversely, the global chord upper bound proves
that every admitted real lift produces an AC complex curve. `lift_roundtrip`
is interval equality, not equality of arbitrary outside values.

The angular value and input energy are ordinary integrals of the original
complex curve and its derivative. Interior eventual equality, then a.e.
congruence, proves angular integrability, winding/endpoint periods, the
squared-speed identity and an explicit finite-energy equivalence. Totalized
energy equalities alone assert no integrability. Finite energy is a separate
guard on class minimization and equality rigidity.

The derived integer endpoint determines an actual finite computational trace,
including composition and reversal. `representative_homotopic` constructs a
homotopy in the additive circle through the existing affine representatives;
it does not assume a computational representative or a homotopy witness.
The actual unit and harmonic cochain periods of that trace equal the input's
angular period and its mean-weighted version. Raw computational traces are
admitted without smoothing and recover their existing lifts on the interval.
Finite-word circle classification is classical and prior campaign context.

The audience is verified nonsmooth curve integration and computational-path
semantics. The covering construction credits
[Hatcher, Algebraic Topology, section 1.3](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf);
the curve-energy context credits
[Calegari, Introduction to Differential Geometry, section 5.1](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf).
The strengthened AC statement is proved here from the pinned inequalities and
finite-interval definition. Classical novelty or editorial acceptance is not
claimed. This builds on
[PR69](https://github.com/Arthur742Ramos/Math-Formalization/tree/dc936b47c4dad84455e82e7104ee3411f27f4a83/computational-hodge/unit-circle-geometry)
and the user's actual computational-path source. Complete used declarations and
proofs retain exact authenticated Git fragments. Unused finite-corner,
paused-example and old circlePath wrapper families remain in their published
predecessors. MIT and Apache-2.0
attribution are preserved. OpenAI Codex supplied new proofs and packaging;
independent review is internal AI review, not human or external peer review.

This concerns the explicit complex unit circle. It is not a general manifold,
de Rham or Kahler analytic Hodge theorem, an intrinsic tangent-bundle comparison,
a Sobolev completion or a numerical algorithm. The angular covector is not
claimed closed on the whole plane. Homotopies stay in the actual circle;
ambient-plane homotopy does not retain winding. Endpointwise/global derivative
claims across clamping and all-AC finite energy are not asserted.

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. Ordered modules
generate identical proof-complete Challenge/Solution surfaces. Run `lake build`,
`python3 scripts/check_package.py --upstream-root PATH`, and
`python3 scripts/check_interfaces.py`. Literal definition values, complete
definition-value closure, normal selected-theorem proof freedom, random aliases
and rejected controls supplement the unchanged canonical verifier. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. Imported definitions
and critical producers have pinned evidence and separate semantic builds.
All required validation runs locally under AGENTS.md. Exact-source kernel/full
canonical, rendering/browser, packet and independent final reviews have separate
source-bound receipts; these requirements alone claim no release completion,
registry submission or acceptance.

The surface generator removes empty code lines outside comments and strings and
reflows ordinary top-level declaration signatures to meet the unchanged source
budget. It joins no proof-body lines or `open` commands. Retained proof bodies
remain complete; fresh elaboration, exact interfaces, kernel replay and source
review are required rather than treating lexical correspondence as Lean
equivalence. The surface manifest records every source digest and transformation.
