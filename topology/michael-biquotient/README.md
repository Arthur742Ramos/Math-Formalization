# Michael's biquotient-map theorems

This nested Lean package formalizes Ernest Michael's Theorems 1.2 and 1.3 from
*Bi-quotient maps and cartesian products of quotient maps*, Annales de l'Institut
Fourier 18(2), 287–302 (1968),
[primary paper](https://www.numdam.org/article/AIF_1968__18_2_287_0.pdf).
These are classical theorems. Michael acknowledges Hájek's priority for the
equivalent limit-lifting characterization and Theorem 1.3.

Continuous surjections are biquotient when every open cover of a fiber has a
finite subfamily whose images contain a neighborhood of the target point.
The package proves arbitrary indexed products are biquotient, with no separation
assumptions. For Hausdorff targets it proves the full equivalence between
biquotience, quotient products with every identity map, and quotient products
with identities of paracompact spaces. The reverse tests are in the target's
universe; this suffices because the explicit Hausdorff paracompact witness is
a copy of the underlying target set. The forward theorem permits an independent
test-space universe.

The filter/ultrafilter bridge is proved from the ordinary cover definition.
The reverse proof constructs a one-point filter topology from an ultrafilter
whose inverse-image filter has no cluster points. It proves that topology is
Hausdorff and paracompact and proves that the deleted diagonal is not closed
while its inverse image is closed. It preserves every member of the failing
fiber cover, avoiding a coverage-destroying reading of Michael's normalization.

The primary declarations are listed in `comparator.json`. `Solution` publicly
imports the proof module. `Challenge` is a byte-identical, self-contained copy
of that module with only canonical Mathlib imports, so its transitive closure
contains no project-specific dependency and no theorem holes. It has more than
300 lines and will receive Palomar's readability warning; it remains below the
1,000-line/100-KiB hard caps. This choice also makes the definition values and
complete statements directly inspectable, without an unspecified definition.

The research audience includes general and categorical topologists working
with quotient products, descent, and topological monoids. See the concrete
later uses recorded in `AUDIT.md`. Neither novelty nor Palomar acceptance is
claimed.

Lean is pinned to `4.35.0-rc2`; canonical Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Run from this directory:

```sh
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

`scripts/check-local.ps1` checks against the installed read-only Windows cache;
its local paths are specific to this execution environment. Hosted preflight
must reconstruct the canonical dependencies and run Comparator, NanoDa and
Lean/con-ron before submission readiness can be claimed.

Authorship and maintenance remain with Arthur Freitas Ramos. Implementation,
source audit, and independent internal review contributions from AI agents are
disclosed in `formalization.yaml` and `REVIEW.md`; no human peer review is claimed.
The repository-root Apache-2.0 license applies to this package. Registry
submission and a default-branch merge require the parent's final approval.
