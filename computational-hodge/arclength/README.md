# Constructed variable-density circle path-energy minimizers

For any positive continuous coefficient rho on the actual period-one additive
circle, this project constructs normalized arclength tau(x)=integral_0^x rho/mean(rho),
its actual homeomorphism inverse, and the admitted absolutely continuous path
N(t)=tau-inverse(n*t). It proves derivative and Lipschitz bounds rather than
assuming a coordinate change or a minimizing bridge.

With the coordinate convention ds=rho dx, path energy is the ordinary integral
of (rho(L(t))*Lprime(t))^2 on [0,1], with no factor 1/2. For an admitted real lift
L, weighted finite energy is proved equivalent to flat finite energy of tau∘L.
The energy identity reduces the minimization to the predecessor's proved flat
path result. The minimum is (mean(rho)*n)^2, attained by N; equality holds exactly
when the competitor equals N at every point of the closed interval. Arbitrary
extensions outside that interval are unrestricted.

The candidate has an actual endpoint-fixed circle homotopy to L. Any admitted
finite-energy competitor in that actual circle homotopy class has at least its
energy, with the same interval rigidity. Every raw computational trace yields an
admitted finite weighted-energy lift. The new `computational_minimum` identifies
the constructed path's energy with the square of that actual trace's period
against the finite harmonic cochain `meanHarmonic rho`. The trace composition,
reversal, realization and harmonic cochain definitions are retained from the
user's indexed binary computational-path definitions, not replaced by a supplied
period bridge. For rho(q)=2+Re(toCircle(q)), a proved strict inequality shows the
flat affine unit loop is not a minimizer. This is a variable-density actual-path
extension of PR68 and PR71's coefficient Hodge result.

This is a classical one-dimensional analytic construction connected to genuine
computational paths. It does not establish a general analytic/Kahler Hodge or
de Rham theorem, an intrinsic manifold metric/cotangent-bundle identification,
a numerical algorithm or arbitrary nonrectifiable path integration. Period-one
dx is not identified with complex-circle arclength including the factor2*pi.
Positivity is continuous positivity on the compact circle; C1 density is not
an extra hypothesis. Totalized integrals alone never assert finite energy.

Classical length, energy and geodesic background is credited to
[Calegari, section5.1 and chapter6](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf).
The user's [computational-path paper](https://arxiv.org/abs/2608.04228v3) and pinned
TopologicalComputationalPaths source supply actual trace definitions. Complete
used predecessor proofs have immutable source mappings; predecessors are not
claimed as new. Mathlib supplies ordinary integration, order homeomorphisms,
inverse differentiation, AC calculus and the circle quotient foundations.
The audience is formalized one-dimensional metric energy and computational-path
semantics. Novelty and editorial acceptance are not promised. Established project
authors and responsible maintainers are distinct from the four paper authors.
OpenAI Codex supplied the new proofs and packaging. Independent review is internal
AI review; no human mathematical or external peer review is inferred. Upstream
MIT/Apache attribution is preserved.

## Source and verification

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. The surface generator
retains every declaration and complete proof from the listed modules, removing
module/import/visibility directives and empty code lines and reflowing ordinary
declaration signatures. No proof-body or open-command lines are joined. Fresh
Lean and kernel checks establish more than lexical preservation. Challenge and
Solution share one implementation; they are not independent proofs.

Run `lake build`, `python3 scripts/check_package.py --upstream-root PATH`, and
`python3 scripts/check_interfaces.py`. Definition values and closure, ordinary
theorem proof freedom, aliases and rejected controls supplement unchanged
canonical verification. Only propext, Classical.choice and Quot.sound are allowed.
Material imported definitions have exact pinned evidence and separate semantic
builds. Dependency cache reuse is disclosed in each receipt.

All required validation is local under AGENTS.md. Exact-source native/kernel/full
canonical, rendering/browser, packet and independent final review outcomes belong
to immutable external receipts. These requirements alone claim no completed
release, registry submission, editorial acceptance or registration.
