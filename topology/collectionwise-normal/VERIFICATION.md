# Historical canonical verification and later source corrections

Evidence inspected on 2026-10-18. These completed receipts identify an immutable
source; they do not claim that a later correction passed the same run.

- Source: `8ba7d5096d7d77a1e2f6e6f04ba70c85aed2a814` in `Arthur742Ramos/Math-Formalization`.
- Project: `topology/collectionwise-normal`.
- Comparator: `topology/collectionwise-normal/comparator.json`.
- Comparator SHA-256: `f09476f92ddd8f1ec05c93592cc23d78763f49323ae05ac30ec88f484510fefc`.
- Verified metadata SHA-256: `39d7bc8b6ed87e994650fc89cb92e04d46a925c68f9ee1e21bd6a294ee804414`.
- Pipeline: `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
- Lean: `leanprover/lean4:v4.35.0-rc2`; compiler `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`; all nine package-owned lockfile revisions preserved.
- Lockfile SHA-256: `cf6afa54703525030ace9d7f3fba7f6406f18afe5c5b0616ead655ccf0991c24`.

[Official full run 39137267489](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39137267489)
passed for this source. Original report: `status: pass`, `stage: complete`, empty
errors and warnings. Protected comparison covers all five theorems and both
definitions with high-trust Challenge provenance and no untrusted sources.
Lean default, NanoDa and con-ron accept; con-ron verifies 5,470 exported declarations.
Report checked at `2026-10-18T14:47:24Z`; original report SHA-256:
`b80eb2d2c3b31b9d371ac9b14d26bb8ba6d1a1eaba0a546733f75463e6095eaf`.
Artifact 12139769563 ZIP SHA-256: `016c99fdbea9107ab4c287fe858fed46ac1a36abe60717988728db2c3bc9eb15`.
The preceding [repository preflight 39133762319](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39133762319)
independently passed for this same source and contract.

[Rendering run 39133762212](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39133762212) separately passed
for that source. Report SHA-256: `1e467102fccd30437fca446973523e04d128be4ce3e47d47e35a2e4597d0cfc4`.
Rendered artifact tree: `af81a0236218556943d648d31f9bcc9ff5a6309849dae1091979a086a80cfe8c`.
All seven surfaces and all 21 artifact file hashes were independently checked.
Static HTML checks are not a browser visual review.

## Later commits and service stages

A status-only correction preserves all Lean proofs, Comparator selections,
package pins and attribution, but changes source bytes. Historical report hashes
continue to refer to the old metadata and source. A new full report must bind
any later proposed intake commit and its actual metadata digest. Later rendering
also needs its own source-bound receipt; proof or Challenge equality alone is
not that receipt. No self-referential future commit hash belongs in this file.

Current editorial, private-attempt and registration state must be reconciled
from the service before another intake. Passing kernels, rendering and internal
AI review do not establish editorial acceptance or public registration.
Private receipts and review text are not published here. This historical record
can remain unchanged after future checks; report the new source externally.

Machine-readable provenance: [verification/canonical-history.json](verification/canonical-history.json).
