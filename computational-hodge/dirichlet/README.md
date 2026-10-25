# Minimum-energy computational circle representatives

This project proves a variational theorem for the actual based loops obtained
from the user's computational paths on the explicit period-one flat real circle.
An admitted real lift is absolutely continuous on `[0,1]`, starts at zero, and
ends at an integer modulo one. Finite energy explicitly means integrability of
the square of its actual derivative. Energy is defined through this actual real lift; no separate Riemannian tangent-bundle identification is claimed. Energy is the ordinary interval integral
`E(L)=∫₀¹(L')²`, without the optional classical factor `½`.

The exact identity `E(L)=L(1)²+∫₀¹(L'−L(1))²` yields the lower bound.
The equality case is proved using a.e. derivative equality and AC constancy:
`E(L)=L(1)²` iff `L(t)=L(1)*t` for every `t∈[0,1]`.
Uniqueness concerns interval values, not global functions outside that interval.
An actual endpoint-fixed projected homotopy is constructed by linear interpolation
of real lifts. The affine representative has finite energy and minimizes energy
among all admitted finite-energy lifts in the actual based homotopy class.

Every finite computational trace embeds using its actual covering lift, without
smoothing; its projected path is literally the user's original realization.
Its finite energy is derived from the proved global Lipschitz bound and actual
measurability and boundedness of the derivative. The minimum is the square of
the actual unit-cochain period, equivalently the integer winding count squared.
The retained mean harmonic cochain belongs to actual `Closed ∩ Exactᗮ`;
`(mean α)² E(minimizer) = period(p,meanHarmonic α)²` is proved.
The actual paused trace `single.trans(refl 0)` has winding one but energy
strictly greater than one, whereas its affine representative has energy one.
The midpoint obstruction proves strictness; no exact energy-two claim is made.
Thus energy depends on parameterization even though winding and harmonic periods
depend only on the based homotopy class.

## Scope and attribution

This is the unique minimum-energy **real lift on the interval** for the explicit
flat circle. It adds a variational connection to actual computational-path
realization. PR65's coefficient energy splitting and PR67's AC integral period
formula are prior results; variance algebra alone is not presented as the new
contribution. Classical Dirichlet minimization and constant-speed principles are
credited to [Calegari, Introduction to Differential Geometry, §5.1](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf)
and [Gantumur, The Dirichlet Problem as a Minimization Problem](https://www.math.mcgill.ca/gantumur/math580f18/dirichletnotes.pdf).
The audience is verified variational analysis and computational-path semantics.
Novelty and registry significance are not guaranteed by machine checks.

The actual endpoint-indexed trace syntax, binary composition, reversal and
realization are retained from the user's [paper](https://arxiv.org/abs/2608.04228v3)
and pinned repository. Exact complete predecessor fragments are mapped to
[PR67](https://github.com/Arthur742Ramos/Math-Formalization/tree/2a2e0ea39a2decd56d338d2a329ee7035bea2628/computational-hodge/ac-lifts).
MIT upstream and Apache-2.0 Mathlib attributions remain. Project authors and
responsible maintainers retain their established roles; these are distinct from
the paper's author list. New proof and packaging work is by OpenAI Codex.
Independent review is internal AI review, not human or external peer review.

Finite energy is essential: a totalized Bochner integral is not evidence of
integrability. No general manifold/de Rham/Kähler Hodge theorem, Sobolev-space
completion, Laplacian, arbitrary continuous-loop integral, reparameterization
invariance, or numerical algorithm is claimed. This is not a proof that all AC
lifts have finite energy. No registry action is implied.

## Source and validation

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. Ordered modules
generate proof-complete Challenge and Solution surfaces by removing only module,
import and visibility directives. Both share one implementation. Complete
dependencies remain visible in public source and static HTML; original rendering
limits and runtime are unchanged.

Run `lake build`, `python3 scripts/check_package.py --upstream-root PATH` and
`python3 scripts/check_interfaces.py`. Exact native interfaces, literal values,
complete definition-value closure retaining normal selected-theorem proof freedom, random aliases and four rejected negative
controls supplement the unchanged canonical verifier. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. Imported definitions and critical
theorem contracts have pinned evidence and separate Challenge/Solution semantic
audits. All necessary validation runs locally under AGENTS.md. Exact-source
canonical full, independent kernels, original rendering, browser, packet and
independent final review have separate source-bound receipts. These requirements
alone do not claim release completion, submission or acceptance.
