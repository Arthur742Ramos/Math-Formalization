# Compact circle Green operator and computational periods

For every positive C1 density rho on the period-one circle, this proves that
PR74's actual Green solution map G_rho is a compact operator on

H_rho = {f : ContinuousMap Circle R | mean(rho*f)=0},

with the ordinary inherited supremum norm. This is the actual closed Banach
subspace, not a supplied abstract solver or an assumed compactness bridge.
Its membership is equivalent to vanishing of every actual weighted raw
computational-trace integral and the retained finite harmonic-cochain periods.
The user's indexed binary traces, actual circle realization, raw-lift regularity,
ordinary integrability and all-cell harmonic closedness proofs remain present.

The proof starts from the proved Green value and coordinate-gradient estimates.
On a forcing ball of radius B, max(0,B) gives a common value bound
4*mean(rho)^2*max(0,B) and a real-cover Lipschitz bound
2*mean(rho)*supnorm(rho)*max(0,B). A negative-radius ball is empty.
These are derived estimates, not compactness or regularity hypotheses.

The real-cover family descends through the actual circle quotient.
Equicontinuity is expressed as continuity of the curried map into UniformFun,
whose topology is uniform convergence over the family index. Pointwise
function-space continuity would not prove this step. Pinned Mathlib's classical
Arzela-Ascoli theorem then gives compact closure in bounded continuous functions.
The actual C0 function-space homeomorphism and the closed H_rho inclusion transfer
that compactness to H_rho. No replacement circle metric is introduced.

Consequently the actual Green image of every bounded forcing set has compact
closure. Every bounded sequence of compatible forcings has a strictly increasing
subsequence whose Green solutions converge in the ordinary supremum norm.
The resulting continuous coefficient has weighted mean zero and actual weighted
raw-trace and finite harmonic periods zero. The source proves these constraints
for the limit; it does not assume them as a separate bridge.

The limit is asserted only continuous and compatible. Boundedness of the forcing
sequence alone gives no C2 certificate, membership of the limit in range(G), or
convergence of any forcing subsequence. No closed-range/coercive lower bound,
Hilbert self-adjoint realization, spectral theorem, Rellich/Sobolev theorem,
general Fredholm/manifold/Kahler Hodge/de Rham result, intrinsic cotangent metric
identification, complex-circle arclength 2*pi identification or numerical solver
is claimed. An actual nonzero Green value for every admitted density follows
from the cosine-Laplacian forcing and proved injectivity, excluding a zero-map
compactness example.

This is a classical one-dimensional analytic compactness result.
[Calegari, Proposition 9.3.4(2) and Theorem 9.3.6(1), in Section 9.3](https://math.uchicago.edu/~dannyc/courses/riem_geo_2019/differential_geometry.pdf)
explain the role of compactness of controlled Laplacian families in the general
Hodge argument. The present proof uses C0 Ascoli directly; it does not formalize
that source's Sobolev/Rellich route. Mathlib's pinned Ascoli and compact-operator
infrastructure are credited. The user's computational-path paper/definitions and
PR65/67/71/73/74 provide actual traces, ordinary integration, positive density,
Poisson construction and Green estimates. The audience is analytic Hodge
formalization with genuine computational-period obstruction semantics. No novelty
or registry acceptance is promised.

Established project authors and responsible maintainers retain their distinct
roles; they are not inferred from the paper's author list. OpenAI Codex supplied
the new proofs and packaging. Independent review is internal AI review, not human
or external peer review. Upstream attribution and MIT/Apache licenses are preserved.

## Source and verification

Lean 4.35.0-rc2/compiler 11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned.
All required predecessor declarations and complete proofs are retained as exact
Git fragments of PR74's accepted source. Only unused whole corollaries are omitted;
retained statements, definitions and proofs are unchanged. Trusted import reduction
uses authenticated public-import paths. The formatter removes empty code lines
and reflows ordinary signatures, joining no proof-body or open-command lines.
Challenge and Solution share one implementation; they are not independent proofs.

Run lake build and the package provenance/interface checks. Separate Challenge
and Solution semantic bridges, exact definition values and full value closure,
rejected controls, aliases and transitive standard-axiom audits supplement the
unchanged full canonical verifier and renderer. Only propext, Classical.choice
and Quot.sound are allowed. Material definitions and important producers have
literal pinned evidence; hashes alone do not establish fidelity. Cache reuse is
disclosed by individual receipts.

All validation runs locally under AGENTS.md. Exact-source build/kernel/canonical,
render/browser, packet and independent final-review outcomes belong to immutable
external receipts. These requirements alone claim no completed release, registry
submission, editorial acceptance or registration.
