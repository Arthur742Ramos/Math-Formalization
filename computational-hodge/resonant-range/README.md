# Resonant circle range and computational-path compatibility

For every positive C1 density `rho` on the period-one real circle, every real
shift `mu`, and every continuous real forcing `f`, this package proves:

```text
exists normalized actual C2 u, Delta_rho u - mu*u = f
iff
all actual raw computational-trace periods of rho*f vanish
and
integral rho*f*v = 0 for every normalized actual C2 v with Delta_rho v - mu*v = 0.
```

Here `Delta_rho u = -rho^(-1) * (u'/rho)'` has the inherited geometer sign,
and normalized means `integral rho*u = 0`. The pairing is the ordinary weighted
integral on the actual circle. The theorem quantifies over every admitted
density and shift; it assumes neither nonresonance nor the desired solution.
The finite harmonic-cochain period criterion is proved equivalent. At zero
shift the additional normalized-mode condition disappears, recovering exactly
weighted period compatibility.

The construction uses the already proved compact Green operator on the closed
C0 compatibility Banach space. The literal weighted pairing defines a closed
subspace orthogonal to its reduced kernel. Symmetry makes that subspace
invariant; strict positivity eliminates the restricted eigenvalue1. The pinned
Banach-space Fredholm theorem then supplies a preimage, and the actual Green
construction reconstructs C2 regularity and the differential equation.
Continuity in the C0 norm and completeness of the closed subspace are proved.
No equality between a C0 norm and an integral-pairing norm is assumed.

This fills the resonant sufficiency gap left by PR76 and PR77. The statement
is for the normalized `Domain`; it is not an unrestricted-forcing assertion
about all unnormalized C2 functions. PR77 supplies a concrete flat cosine
resonance and demonstrates why period compatibility alone is insufficient.
The present theorem supplies the missing additional condition rather than
relabeling that obstruction.

The path model remains the user's literal indexed binary geometric traces:
composition, reversal, actual continuous realization, covering lifts and all
finite trace corners are retained. Ordinary projected-curve integrability,
the actual-realization bridge, and finite cochain harmonicity remain explicit.
This is a circle analytic result connected to those computational paths;
it does not identify the model with an intrinsic manifold cotangent complex.

The complete generated Challenge and Solution contain every required retained
custom declaration and proof. Seventeen immutable public-Git fragment mappings
and exact-statement proof-refactor chains preserve full original/replacement
texts. Ordered header consolidation and editorial whitespace reflow are
recorded separately from mathematical proof changes. No proof-body formatter
joins or increased source/output limits are used. Both entrypoints share one
implementation, and are not independent proofs.

Classical compact-operator Fredholm theory is credited to the pinned library;
[Tao's exposition, section2](https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/)
provides the Riesz-lemma context. The construction here uses the general
compact-operator theorem, without a finite-rank approximation assumption.
The actual weighted pairing, invariant-subspace transfer, C2 reconstruction
and computational-period equivalences are proved in the retained source.
No mathematical novelty or registry acceptance is claimed.

There is no general manifold/Kahler Hodge or de Rham theorem, spectral
basis/completeness claim, Hilbert completion or unbounded self-adjoint domain,
canonical orthogonal representative, uniform near-resonance bound, or numerical
solver. Source-bound native, semantic, interface/value-closure, negative-control,
axiom, kernel, canonical, rendering, browser and packet outcomes are recorded
in separate immutable release receipts.

OpenAI Codex supplied the substantive new proofs and packaging. Separate
internal AI review is distinct from human or external peer review. Established
author and responsible-maintainer roles remain separate and do not imply human
proof contributions. Existing MIT/Apache attribution and exact Lean4.35.0-rc2
compiler11acb17ec6b07a8f9e9173e6845197929540936b / Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55
pins are preserved. All necessary validation runs locally; author-hosted CI
remains retired. No registry action is part of this development package.
