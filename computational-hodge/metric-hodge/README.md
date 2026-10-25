# Positive-density circle Hodge representatives and computational periods

This project changes the analytic metric coefficient model from the flat circle
to an arbitrary positive continuous length density rho on AddCircle(1). In the
fixed period-one coordinate x the convention is ds=rho dx, hence g=rho^2 dx^2.
The ordinary one-form energy of alpha is

```text
E_rho(alpha) = integral_0^1 alpha([x])^2 / rho([x]) dx.
h_rho(alpha) = (mean(alpha) / mean(rho)) * rho.
```

Integrability and mean(rho)>0 are proved from continuity, positivity and the
actual compact-circle Haar measure. Energy is first defined by ordinary circle
integration and proved equal to the displayed coordinate interval integral.
It is one-form coefficient energy, distinct from path-velocity energy.

The coordinate stars are star_0(phi)=phi*rho and star_1(alpha)=alpha/rho.
Both inverse identities are proved. The degree-correct coordinate codifferential
is delta(alpha)=-(alpha/rho)'/rho. MetricHarmonic explicitly requires
differentiability of alpha/rho before requiring delta(alpha)=0, since Lean's
derivative is totalized at nondifferentiable points. The proof derives that this
condition is equivalent to alpha=c*rho. A genuine integration-by-parts identity
proves the coordinate adjoint formula against C1 periodic test potentials when
the ratio alpha/rho is C1. These extra C1 hypotheses belong to that adjoint
theorem; they are not silently imposed on every continuous input.

The representative h_rho(alpha) is proved harmonic and has the same mean.
The proof constructs an actual continuous circle potential whose real cover is
C1, is zero at the basepoint and has derivative alpha-h_rho(alpha). Weighted
orthogonality gives a Pythagorean identity. Zero weighted energy forces the
coefficient to be zero at every circle point, not just almost everywhere.
Consequently the harmonic representative is the unique energy minimizer among
all coefficients differing from alpha by an analytic exact coefficient, with
minimum mean(alpha)^2/mean(rho).

The density rho(q)=2+Re(AddCircle.toCircle(q)) is proved positive and nonconstant
using its values 3 at zero and 1 at one-half. It is metric-harmonic although it
is not flat-harmonic. Even the metric-harmonic representative of the constant-one
coefficient is proved nonconstant. Thus this is not just a flat constant rescaling.

The actual integration results from PR67 are retained as prerequisites. For every
interval-absolutely-continuous real lift and every actual unsmoothed finite
computational trace, replacing alpha by h_rho(alpha) preserves its ordinary
line integral. These integrals equal the periods of the retained finite harmonic
cochain meanHarmonic(alpha). The analytic metric-dependent coefficient and that
finite harmonic cochain are distinct objects. Their proved connection is through
actual periods; they are not identified as definitions or as metric structures.
The actual unit trace proves nonvacuous period detection of analytic exactness.

## Scope, classical context and attribution

This is an explicit continuous-density coefficient model, relative to period-one
dx. It is not an intrinsic Riemannian cotangent-bundle or manifold Hodge
identification. A classical smooth Riemannian interpretation requires additional
regularity and comparisons that are not asserted here. No identification of dx
with the canonical complex-circle arclength, including its 2*pi factor, is made.
The codifferential output is a real function and is not automatically claimed to
be a continuous circle coefficient. No general manifold/de Rham/Kahler Hodge
theorem, full Laplacian complex, Sobolev completion or numerical algorithm is
proved. Arbitrary continuous nonrectifiable path integration is not asserted.

The classical metric/Hodge-star, adjoint and minimum-energy principles are credited
to [Calegari, sections9.1-9.3](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf).
The user's [computational-path paper](https://arxiv.org/abs/2608.04228v3) and pinned
TopologicalComputationalPaths source provide the actual indexed binary trace,
composition, reversal and realization definitions. PR65 supplies the actual circle
potential, PR67 the nonconstant-coefficient AC integration bridge, and later
projects the reduced exact source dependencies. None of those prior results is
claimed as new here. Mathlib supplies the pinned ordinary integration, calculus,
covering and measure foundations. The audience is formalized metric-dependent
one-dimensional Hodge theory and computational-path semantics. Novelty and
editorial acceptance are not promised. Established project authors and responsible
maintainers are distinct from the four paper authors; upstream MIT/Apache headers
are preserved. OpenAI Codex supplied the new proofs and packaging. Independent
review here is internal AI review, not human mathematical or external peer review.

## Source and verification

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. Exact predecessor
declaration fragments and complete used proofs have immutable Git mappings.
The AC modules explicitly qualify Circle as CircleHodge.Circle to disambiguate
the additive circle from the newly imported complex Circle; the intended
statements and proofs retain the additive-circle contract. The
surface generator removes module/import/visibility directives and empty code lines,
then reflows ordinary declaration signatures only. It joins no proof-body or open
command lines. Every retained proof remains visible. Lexical preservation alone
does not establish Lean equivalence; fresh builds and kernel checks are required.
Challenge and Solution share one implementation, not independent proofs.

Run lake build, python3 scripts/check_package.py --upstream-root PATH, and
python3 scripts/check_interfaces.py. Literal definition values, complete definition
value closure, normal selected-theorem proof freedom, random aliases and rejected
controls supplement the unchanged canonical verifier. Only propext,
Classical.choice and Quot.sound are permitted. Material definitions and critical
producers have exact pinned evidence and separate semantic builds.

All required validation is local under AGENTS.md. Exact-source native/kernel/full
canonical, rendering/browser, packet and independent final review outcomes belong
to immutable external receipts. These requirements alone claim no completed
release, registry submission, editorial acceptance or registration.
