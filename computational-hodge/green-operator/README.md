# Bounded circle Green operator and computational obstruction

For a positive C1 period-one circle length density rho, put m=mean(rho)>0
and M=the ordinary supremum norm of rho. This constructs a continuous linear
solution map on the actual closed C0 subspace

H_rho = {f : ContinuousMap Circle R | mean(rho*f)=0}.

The norm is the ordinary supremum norm on continuous functions, inherited by
the subspace. Its completeness follows from closedness in that Banach space.
Membership is proved equivalent to vanishing of every actual raw computational
trace integral of rho*f, and to vanishing of its retained finite harmonic-cochain
periods. The user's endpoint-changing binary traces and their actual circle
realization remain the underlying model. The raw-realization bridge, ordinary
integrand integrability and all-cell harmonic closedness proofs are retained.

The solution uses PR73's actual two periodic primitives and weighted-mean
normalization. No Green solver or bound is supplied as an assumption. Direct
integral estimates and positivity of rho prove, for every compatible forcing,

- supnorm(G f) <= 4*m^2*supnorm(f);
- supnorm((G f)') <= 2*m*M*supnorm(f);
- supnorm((G f)'/rho) <= 2*m*supnorm(f).

These conservative constants are not claimed sharp. The derivative is the
coordinate derivative of the real periodic cover. All three statements concern
actual continuous coefficients. The first estimate constructs the actual
ContinuousLinearMap H_rho H_rho; it also gives difference/stability bounds.
The separately stated scalar operator-norm inequality is not a formal target.

Every image has an actual C2 certificate. The operator
Delta_rho u = -((u'/rho)')/rho gives a right inverse on H_rho, and applying
G to Delta_rho u recovers the weighted-mean normalization of u. The image in
H_rho is proved exactly the C2 elements. This does not declare the inherited
supremum norm C2 subspace complete, or define a Laplacian on all C0.

The ordinary weighted integral pairing satisfies
integral(rho*f*G g)=integral(rho*g*G f) and is strictly positive on (f,G f)
for nonzero compatible f. For every admitted density, Delta_rho applied to the
actual C2 cosine is a concrete nonzero compatible forcing with positive pairing.
The forcing is defined by the actual operator; no closed trigonometric forcing
formula or numerical solver is claimed.

This is a classical one-dimensional coordinate analytic result. Pairing symmetry
is not a self-adjoint Hilbert-space realization, and strict positivity is not a
uniform coercive lower bound. No closed-range, compactness, spectral, Sobolev,
weak elliptic regularity, general Fredholm or manifold/Kahler Hodge/de Rham
theorem is asserted. Period-one dx is not identified with complex-circle
arclength and its2*pi factor.

The primary classical Laplacian/adjoint and elliptic-estimate context is credited
to [Calegari, Sections9.2-9.3](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf).
The precise C0 estimates above are derived in this package rather than quoted
as that source's theorem. The user's computational-path paper and pinned
TopologicalComputationalPaths definitions supply actual traces; PR65/67/71/73
supply periodic primitives, actual raw integration, density infrastructure and
the coordinate Poisson construction. PR72's path-energy minimization is distinct.
Mathlib supplies ordinary calculus, normed continuous-function spaces and
integration. The audience is formalized analytic Hodge theory with stable
computational-path obstruction semantics. Novelty and registry acceptance are
not promised.

Established project authors and responsible maintainers are distinct from the
paper's author list. OpenAI Codex supplied the new proofs and packaging.
Independent review is internal AI review, not human or external peer review.
Upstream attribution and MIT/Apache licenses are preserved.

## Source and verification

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned.
Exact complete predecessor fragments and statement-preserving proof adaptations
are recorded separately. Adaptations derive continuity from proved Lipschitz
regularity, reuse actual isometry/scalar facts and compose calculus proofs.
Unused whole corollaries are omitted. All required custom declarations and
complete proofs remain visible. Redundant trusted Mathlib imports are removed
only through authenticated public-import paths. The surface formatter joins no
proof-body or open-command lines. Challenge and Solution share one implementation;
they are not independent proofs.

Run lake build and the package provenance/interface checks. Separate Challenge
and Solution semantic bridges, exact definition values and their complete value
closure, rejected controls, aliases and transitive standard-axiom audits supplement
the unchanged full canonical verifier and original renderer. Only propext,
Classical.choice and Quot.sound are allowed. Material definitions/producers have
exact pinned evidence. Cache reuse is disclosed per receipt.

All validation runs locally under AGENTS.md. Exact-source build/kernel/canonical,
rendering/browser, packet and independent final-review outcomes belong to immutable
external receipts. These requirements alone claim no completed release, registry
submission, editorial acceptance or registration.
