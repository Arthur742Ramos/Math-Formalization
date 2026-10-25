# Actual unit-circle angular periods and energy

This project connects actual computational-path realizations to the canonical
complex unit circle and to ordinary differential-form and energy integrals.
It builds on PR68's real-lift Dirichlet theorem rather than defining a new
geometric energy as a scalar multiple of that theorem's energy.

`embed` is the actual pinned `AddCircle.toCircle` followed by coercion to `ℂ`.
Its real-coordinate formula is `exp(2πix)` and its norm is one. The actual
`circlePath` stays in the unit-circle subtype; its basepoint is proved equal
to one. `curve` is the ambient complex realization, clamped outside `[0,1]`.
For any admitted interval-absolutely-continuous lift `L`, the actual real
chain rule proves, in the interval interior wherever the lift is differentiable,

```text
curve'(t) = curve(t) * i * (2π L'(t)).
```

Absolute continuity then gives this formula almost everywhere on `[0,1]`.
There is no global or endpointwise derivative assertion across the clamp.

`angularForm z` is an actual real-linear covector on `ℂ`, with value
`Im(conj(z)*v)/(2π)`. Its pullback along the actual curve equals `L'` a.e.
Consequently the angular integrand is integrable for **every** admitted AC lift,
and its ordinary interval integral is `L(1)`. No finite-energy hypothesis is
needed for this angular result. For an actual computational trace it is exactly
the actual unit-cochain period. Multiplication by `mean α` gives the period of
the retained actual mean harmonic cochain in `Closed ∩ Exactᗮ`.

The independently proved squared-speed identity gives

```text
∫₀¹ ‖curve'(t)‖² = (2π)² ∫₀¹ (L'(t))².
```

Ambient finite energy is proved equivalent to finite squared-derivative lift
energy. Guarded variational results then transfer the affine minimum and its
rigidity to actual ambient curves. Curve equality is proved equivalent to
equality of real lifts on the interval using canonical embedding injectivity
and actual covering-lift uniqueness. Every actual raw trace has finite energy;
its minimum is `(2π)² period(p,unitCochain)²`. The paused unit trace has energy
strictly greater than `(2π)²`. An actual homotopy to the affine representative
is mapped through the unit-circle subtype.

Competitor homotopies in `ambient_class_minimum` are in the original circle.
Homotopy in the whole complex plane would lose winding information and is
neither assumed nor substituted. The ambient curves compared here have supplied
admitted real lifts; no regular lifting theorem for arbitrary ambient curves is
claimed. The angular covector is normalized on the unit-circle image. The same
displayed field is **not** claimed closed on all of `ℂ`.

## Scope and attribution

The nonduplicate addition is the actual canonical embedding, real chain-rule
pullback of a concrete angular covector, and ordinary ambient squared-speed
comparison. The normalization and variational principles are classical.
[Calegari, Introduction to Differential Geometry, §5.1](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf)
provides the classical curve-energy context (with a conventional factor `½`);
this project uses energy without that factor. Actual `Circle`, quotient-to-circle
map, complex exponential/circle-map derivative, norms and conjugation are credited
to pinned Mathlib. The audience is verified curve geometry, differential-form
integration and computational-path semantics. Novelty or registry significance
is not promised by mechanical checks.

The actual endpoint-indexed trace syntax, composition/reversal and realization
come from the user's [paper](https://arxiv.org/abs/2608.04228v3) and pinned source.
Complete used declarations and proofs are mapped to
[PR68](https://github.com/Arthur742Ramos/Math-Formalization/tree/b4ce30abfa165ad9c4905acbd1dd99813b4ad4e9/computational-hodge/dirichlet).
Unused predecessor declarations are omitted at named declaration boundaries;
retained proofs are complete. Prior packages and their statements are unchanged.
MIT upstream and Apache-2.0 Mathlib attribution remain. Established project
authors and responsible maintainers are distinct from the paper authors.
OpenAI Codex supplied new proofs and packaging; independent review is internal
AI review, not human mathematical or external peer review.

This is not a general manifold/de Rham/Kähler Hodge theorem, intrinsic tangent-
bundle identification, Sobolev completion, arbitrary continuous-loop integral,
ambient-plane homotopy classification, proof that every AC lift has finite
energy, or numerical algorithm. Totalized energy integrals alone do not assert
integrability; `finite_energy_iff` and explicit guards provide that boundary.

## Source and validation

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. Ordered modules
generate identical proof-complete Challenge/Solution surfaces by removing only
module, import and visibility directives. They share one implementation.
Complete dependencies remain visible in public source and static HTML; original
rendering limits and runtime are unchanged.

Run `lake build`, `python3 scripts/check_package.py --upstream-root PATH` and
`python3 scripts/check_interfaces.py`. Exact native interfaces, literal values,
complete definition-value closure retaining normal selected-theorem proof freedom,
random aliases and four rejected negative controls supplement the unchanged
canonical verifier. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Imported definitions and critical producers have pinned evidence and separate
Challenge/Solution semantic audits. All necessary validation runs locally under
AGENTS.md. Exact-source canonical, kernels, rendering/browser, packet and
independent final review have separate source-bound receipts. These requirements
alone do not claim release completion, registry submission or acceptance.
