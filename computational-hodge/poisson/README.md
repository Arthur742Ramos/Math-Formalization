# Weighted circle Poisson solutions and computational-period obstruction

This constructs actual periodic C2 solutions of the scalar equation
Delta_rho u = -((u'/rho)')/rho = f on the period-one additive circle.
The coordinate convention is ds=rho dx. Density rho is positive and C1;
forcing f is continuous. The domain is an actual submodule of continuous circle
functions with C2 real covers. The output is an actual continuous circle
coefficient: derivative periodicity, flux C1 regularity and quotient descent
are proved. Totalized derivatives at arbitrary nonsmooth functions are not
used as a substitute for these contracts.

The equation has a solution exactly when the ordinary weighted mean
integral_0^1 rho*f is zero. The construction uses two genuine ordinary
primitives. First integrate rho*f to a periodic C1 function F. Choose
c=mean(rho*F)/mean(rho), then integrate rho*(c-F), whose mean is proved zero.
The resulting circle potential is proved C2. Subtracting its weighted average
gives a solution with weighted mean zero. Basepoint normalization is not imposed
simultaneously. The kernel is exactly the constants; solutions differ by a
constant, and weighted normalization gives a unique solution.

For arbitrary forcing, `green` constructs the normalized solution after its
weighted constant projection is removed. Its right-inverse and normalized
left-inverse identities are proved. This is a constructed solution map;
linearity and boundedness are not part of its established operator contract.
The actual Green integral identity has the nonnegative geometer's sign:
integral rho*(Delta_rho u)*v = integral u'*v'/rho.
Weighted-pairing symmetry and a nonnegative quadratic form follow, with actual
integrability supplied by the regularity contracts.

Compatibility is also equivalent to vanishing of every actual raw computational
trace integral of the coefficient rho*f, and to vanishing of its periods against
the retained finite harmonic cochain `meanHarmonic (rho*f)`. The actual unit trace
detects the obstruction, so the universal condition is not vacuous. The user's
indexed binary composition/reversal/realization definitions and the prior actual
AC/raw integration bridge are retained with complete proofs. These integration
results are credited predecessors; the new connection is their equivalence to
solvability of the constructed second-order equation. Constant forcing1 is
obstructed for every admitted density. A concrete density2+cos(2*pi*x), actual
C2 cosine solution and proved nonconstant compatible forcing produce a
nonconstant normalized solution. The forcing is defined by the actual operator;
no closed trigonometric forcing formula is claimed.

This is an explicit classical coordinate Poisson solvability alternative.
It does not prove a general functional-analytic Fredholm or spectral theorem,
a self-adjoint Sobolev realization, weak-solution elliptic regularity, an intrinsic
manifold/cotangent-bundle identification, general analytic/Kahler Hodge/deRham
theory, or a numerical solver. Period-one dx is not identified with complex-circle
arclength and its2*pi factor.

Classical scalar-Laplacian, adjoint and Hodge context is credited to
[Calegari, sections9.2-9.3](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf).
The user's [computational-path paper](https://arxiv.org/abs/2608.04228v3) and pinned
TopologicalComputationalPaths definitions supply actual traces. PR65 provides
periodic potentials, PR67 actual AC/raw integration, and PR71 the metric adjoint
model. PR72's actual path-energy minimizers are a distinct preceding result.
Mathlib supplies ordinary calculus, integration and quotient infrastructure.
The audience is formalized one-dimensional analytic Hodge theory and
computational-path obstruction semantics. Novelty and acceptance are not promised.
Established project authors and responsible maintainers are distinct from the four
paper authors. OpenAI Codex supplied the new proofs/packaging. Review is internal
AI review, not human mathematical or external peer review. Upstream attribution
and MIT/Apache licenses are preserved.

## Source and verification

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. Complete used
predecessor proofs have exact immutable Git mappings. The surface generator removes
module/import/visibility directives and empty code lines and reflows ordinary
declaration signatures. It joins no proof-body or open-command lines. All retained
proofs remain visible. Fresh builds and independent kernels establish more than
lexical preservation. Challenge and Solution share one implementation; they are
not independent proofs.

Run `lake build`, `python3 scripts/check_package.py --upstream-root PATH` and
`python3 scripts/check_interfaces.py`. Separate semantic builds, exact definition
values and complete value closure, normal selected-theorem proof freedom,
random aliases and rejected controls supplement unchanged canonical validation.
Only propext, Classical.choice and Quot.sound are allowed. Material imported
definitions and important producers have exact pinned evidence. Cache reuse is
disclosed per run. All validation is local under AGENTS.md. Exact-source
native/kernel/full canonical, rendering/browser, packet and independent final
review outcomes belong to immutable external receipts. These requirements alone
claim no completed release, registry submission, editorial acceptance or registration.
