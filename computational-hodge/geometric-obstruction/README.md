# Geometric harmonic correction and null-loop obstruction

This project continues the computational-path Hodge bridge with a canonical
geometric correction and an exact metric description of the obstruction.
It uses the user's actual endpoint-changing `GeometricTrace`, continuous step
system and sound scoped rewrite presentation. Only the generator type `E` is
finite; vertices and named rules may be infinite, empty or disconnected.

Let `G` be the presentation whose generating relations are actual endpoint-fixed
homotopies between realized traces. In the finite Euclidean edge-coefficient
space, write `N = NullSpan S` for the real span of word chains of actual
nullhomotopic computational loops, and `R = Relations P` for the original
presentation's relation chains. PR61 establishes `Relations G = N` and `R ≤ N`.

The new obstruction space is `O = N ∩ Rᗮ`. For every old harmonic cochain `h`,
define `b(h) = proj_N h` and `g(h) = h - b(h)`. The proofs establish:

- `g(h)` is harmonic for `G` and its periods respect actual realized-path homotopy.
- `b(h) ∈ O`, and `h = g(h) + b(h)` is the unique such orthogonal decomposition.
- The actual quotient map `b ↦ [b]P` is a linear isometric equivalence from `O`
  to `ker(homologyMap P)`.
- For every `k` harmonic for `G`,
  `‖h-k‖² = ‖b(h)‖² + ‖g(h)-k‖²`.
  Consequently `g(h)` is the unique closest geometric harmonic cochain and its
  approximation error is exactly the norm of the kernel class `[b(h)]P`.
- The obstruction is zero exactly when all null-loop periods vanish, equivalently
  when the original cochain's periods already respect actual geometric homotopy.
- A geometrically constant generator supplies a nonzero old harmonic cochain
  whose correction is zero and whose kernel obstruction has positive norm.

The norm on the kernel is the restriction of the existing quotient norm on
`Cycles / ChainBoundaries`: the infimum of the existing cycle norm over a coset.
It is not newly defined by transporting the obstruction norm. The norm proof
uses Mathlib's `quotientEquivOrthogonal` inside the cycle subspace. The package
proves that the concrete quotient map restricts to the geometric kernel, is
bijective there and preserves those already defined norms.

## What this does and does not establish

The generic orthogonal projection, quotient-complement and least-distance facts
are classical library mathematics. The new bridge identifies their actual
geometric obstruction and correction-error meaning for this computational-path
model. Projection is noncomputable/classical; no executable numerical method,
ranking estimator or pseudoinverse is formalized.

Only represented computational paths are in scope. There is no identification
with ambient singular or de Rham cohomology, integral homology, or analytic/Kähler
Hodge theory. Correction can change the original cohomology class. Zero kernel
means no obstruction in the real relation span; it does not imply that the old
rewrite system presents every actual geometric homotopy. No ordinary-product
isometry, novelty, registry acceptance or external peer review is claimed.

## Source and mathematical context

- [PR61 geometric descent](https://github.com/Arthur742Ramos/Math-Formalization/tree/7796c0937290beb0eba7688ab93ebf57b2318e0a/computational-hodge/geometric-descent)
  supplies the retained geometric presentation, null-loop span, incidence-chain
  quotient and homology map. `base-provenance.json` records exact complete
  declaration slices from nine predecessor modules, including full proofs,
  two import changes and namespace closures. Older packages are unchanged.
- [Topological Semantics for Scoped Computational Paths, v3](https://arxiv.org/abs/2608.04228v3)
  supplies the actual path model. `source-provenance.json` retains literal
  excerpts at upstream commit `ea1367d99c7d2f3794f1299cce5b18379e9093a7`, with
  MIT attribution in `SOURCE-LICENSE.txt`.
- [Jiang–Lim–Yao–Ye, v2, Theorems 4.7 and 5.1](https://arxiv.org/abs/0811.1067v2)
  gives classical finite Hodge and least-squares context. Their application and
  algorithm are not claimed as proved here.
- [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55)
  provides the actual finite Euclidean, finite-support, quotient-norm and
  orthogonal-projection definitions. Their exact statements, source hashes,
  license headers and semantic expansions are in `MATERIAL-DEFINITIONS.md` and
  `verification/material-imported-definitions.json`.

The intended audience is researchers formalizing computational-path semantics
and finite cochain models who need to measure the effect of adding actual
geometric relations. This is a focused formalization continuation; neither
novelty nor satisfaction of an external research-interest review is guaranteed.

## Files and reproducibility

`Obstruction.lean`, `KernelMetric.lean` and `MetricExample.lean` contain the new
proofs. Nine source-mapped predecessor subsets provide the dependencies.
`scripts/make_surface.py` copies every retained declaration and complete proof
from all twelve ordered modules, removing only module/import/visibility headers.
`Challenge.lean` and `Solution.lean` share this disclosed implementation.
The generator does not prune proof text to reduce rendered size.

Lean is pinned to `4.35.0-rc2`; the lockfile pins all dependencies. Locally run
`lake --no-cache build`, `python3 scripts/make_surface.py --check`,
`python3 scripts/check_package.py --upstream-root PATH_TO_PINNED_USER_SOURCE`
and `python3 scripts/check_interfaces.py`. These are component checks.
The 47 comparator targets have separate modular, Challenge and Solution axiom
audits. Semantic modules compile independently through each standalone entrypoint,
including the literal coset-infimum norm formula and actual quotient-map laws.

All required verification runs locally under the repository policy. Fresh
exact-source canonical full, rendering, independent kernel, visual and review
outcomes belong in immutable external receipts. The final release packet binds
the actual commit, metadata, comparator, report and source archive. Local native
checks do not imply canonical or registry acceptance; later edits require
affected checks again. Author-hosted CI stays retired.

## Attribution and review

Established project authors and responsible maintainers are Arthur Freitas
Ramos, Ruy Jose Guerra Barretto de Queiroz and David Barros Hulak. These roles
are separate from the cited paper's author list. OpenAI Codex supplied the new
proofs and packaging, with independent internal AI mathematical/source and
evidence review. No human proof contribution, human review or external peer
review is inferred from role assignments. Exact review scopes and machine
results are bound to source in separate receipts; see `REVIEW.md`.
