# Completed mechanical verification and its scope

Evidence inspected on 2026-10-18. This account names immutable completed runs;
it does not infer a result for a later commit.

## Exact source and Comparator

- Repository: `Arthur742Ramos/Math-Formalization`.
- Verified commit: `10f8b9075144c51468729b9b620c46b739c0a680`.
- Project: `topology/sigma-product-frechet`.
- Comparator: `topology/sigma-product-frechet/comparator.json`.
- Comparator SHA-256: `a88221925c316500fd5706a6bfc0144b30e70321ccfa05ae509fb37b8c177a5e`.
- Verified metadata SHA-256: `1a3a69478da0c0212d9a30c3f0081124d7978ac6e4057fefc6e807a8615c32ec`.
- Pipeline: `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
- Lean: `leanprover/lean4:v4.35.0-rc2`, compiler `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`; the package owns its lockfile.

## Completed full verification

[Palomar run 39085577215](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39085577215)
completed successfully on 2026-10-18 at 01:15:38 UTC. Its original mechanical
report has `status: pass`, `stage: complete`, no errors and no structured
warnings. Protected comparison passed for all eight selected theorems and
both definitions. Con-ron accepted 7,125 declarations with verification enabled;
NanoDa and Lean default kernel also accepted. The execution profile was
`palomar-namespace-16x32-v1`, the registry's own dispatch profile.

Original report SHA-256:
`d13896a300e2fee357254432c8c7f4e6f400ee4f09a11e6db8e8ab6f2d68b4a9`.

Artifact 12120802032 ZIP SHA-256:
`d03ad4d1616ad949abc34bb1c2db45ebf605cf9d205275ddddfbc80e5a72e8b3`.

## Separate rendering and review evidence

[Canonical rendering run 39083465499](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39083465499)
passed for the same source, selecting the same eight theorems and two
definitions. Its report SHA-256 is
`f4b1004cbbcab33b556cd91328e2770c3b53574ae2afcda96315ddd7b7750635`.
The rendering report and published file hashes are evidenced; a browser
visual review is not claimed.

The dated internal AI review scopes remain in [REVIEW.md](REVIEW.md).
They are not human or external peer review. Mechanical verification and
rendering do not establish editorial acceptance or public registration;
current private review/intake state and duplicate clearance remain separate.
No private review text or private access link is published here.

## Applying this record to later commits

The reports above apply only to their named source commit and configuration.
They do not certify a later metadata or documentation correction. Before
intake of another commit, its own full report must bind that exact commit,
project paths and Comparator and pass. That later report is the evidence for
the new commit; this historical account need not be edited to claim it.
New rendering or editorial results likewise require their own receipts.

Machine-readable provenance: [verification/canonical-history.json](verification/canonical-history.json).
