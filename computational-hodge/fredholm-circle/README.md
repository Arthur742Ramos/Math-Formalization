# Shifted circle Laplacian and computational periods

For every positive C1 density rho on the period-one circle and every real shift
mu, this proves a Fredholm alternative for the actual weighted-circle Laplacian.
The domain D_rho consists of actual C2 circle coefficients with weighted mean
zero. The forcing space H_rho is the actual closed weighted-mean-zero subspace
of continuous circle coefficients, with its ordinary supremum norm.

Exactly one branch holds:

- A nonzero normalized C2 coefficient satisfies Delta_rho u = mu*u.
- Every forcing in H_rho has a unique normalized C2 solution of
  (Delta_rho - mu)u = f.

The proof transfers PR75's actual compact Green operator, rather than assuming
an inverse or regularity bridge. It proves that laplaceData and liftData are
inverse maps between D_rho and H_rho as underlying sets. No continuity of the
Laplacian for the C0 norm is asserted. Under this identification the differential
equation is equivalent to (I - mu*G_rho)x = f. Pinned Mathlib's generic compact-
operator Fredholm theorem applies to mu*G_rho at the nonzero parameter 1; mu
itself may be zero. The source separately proves nonresonance at zero.

Outside resonance, the constructed map

S_rho,mu = G_rho composed with (I - mu*G_rho)^(-1)

is an actual continuous linear map H_rho to H_rho. Its output has a proved C2
representative in D_rho solving the differential equation. A proved bound
norm(S f - S g) <= C*norm(f-g), with C nonnegative, gives stability. C may depend
on rho and mu; no explicit or uniform bound near resonance is claimed. At zero
shift this map equals the existing Green map. No Banach structure on C2 is used.

The computational-path connection remains literal. The user's endpoint-indexed
binary traces, ordinary circle realization and actual covering lifts determine
the raw line integrals. H_rho membership is equivalent both to vanishing of all
weighted raw trace integrals and to vanishing of the retained finite harmonic-
cochain periods. Shifted normalized solutions necessarily have compatible
forcing. Outside resonance those actual raw-period conditions are also
sufficient for existence. The constructed solution itself has zero weighted raw
and harmonic-cochain periods. Projection, global lift Lipschitz regularity,
ordinary integrand integrability and all-cell harmonic closedness proofs remain
present; no assumed path-to-analysis bridge replaces them.

This is a classical one-dimensional scalar result. [Tao's 2011 exposition,
second proof](https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/)
explains the Riesz-lemma compact-operator alternative used by the pinned library.
The first proof there has an approximability restriction and is not the route
claimed here. Mathlib's generic Fredholm theorem is credited; this package proves
the actual weighted-circle differential-equation and computational-period
transfer. It does not claim a new abstract Fredholm theorem or mathematical
novelty. The audience is analytic Hodge formalization with explicit path-period
obstruction semantics.

No spectral basis, eigenvalue enumeration, finite-dimensional resonant kernel,
Hilbert self-adjoint realization, orthogonal forcing criterion at resonance,
Fredholm index theorem, Sobolev/Rellich/weak elliptic regularity, general manifold
or Kahler Hodge/de Rham theorem, intrinsic metric or complex-circle arclength
identification, or numerical solver is claimed. PR75's C0 subsequential limits
are not upgraded to C2 by this result: current C2 solutions are reconstructed
through the actual Green map, not obtained by assuming regularity of a limit.

Established authors and responsible maintainers retain their separate authorized
roles. OpenAI Codex supplied the substantive new proofs and packaging. Separate
internal AI review is not human mathematical review or external peer review.
Existing MIT and Apache attribution is preserved.

## Source and validation

Lean 4.35.0-rc2, compiler 11acb17ec6b07a8f9e9173e6845197929540936b, and
Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. Complete required
predecessor declarations are retained through exact Git fragments of PR75.
Only whole unused corollaries are omitted. Six genuine proof refactors preserve
all statements and definitions and retain complete original and replacement
proofs in proof-refactors.json. Eight trusted imports cover the original 28
through authenticated public-import paths. The formatter removes empty code
lines and reflows ordinary signatures; it joins no proof-body or open-command
lines. All required mathematical content remains visible in complete source.

Run lake build and the package source/interface checks. Separate Challenge and
Solution semantic expansions, exact interfaces/definition values/full value
closure, rejected controls/random aliases and standard-axiom audits supplement
the unchanged canonical verifier, independent kernels and renderer. Challenge
and Solution share an implementation; they are not independent proofs. Material
imported definitions have literal pinned evidence and independent fidelity
review. Hash consistency alone proves neither completeness nor mathematical
meaning. Cache reuse is disclosed by individual receipts.

All validation runs locally under AGENTS.md. Exact-source build/kernel/canonical,
render/browser, packet and independent final-review outcomes belong to immutable
external receipts. These requirements alone claim no completed release, registry
submission, editorial acceptance or registration.
