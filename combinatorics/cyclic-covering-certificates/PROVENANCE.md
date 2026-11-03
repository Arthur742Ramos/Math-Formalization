# Source and port provenance

The original 48 proof modules come from the 3 November 2026 cyclic-covering
research supplement, originally checked with Lean 4.19.0 and Std. This package
ports them to official Lean 4.35.0-rc2 and its bundled Std. The mechanical
source changes add `module`, `public import`, `public section`, and `@[expose]`
on definitions whose bodies clients use. No mathematical declaration statement
or proof body is changed by this initial port. `PORT-MANIFEST.json` binds each
original and ported source hash; fresh compilation is a separate check.

The original internal AI source review applies to the original mathematical
content. It is not a verification of this new toolchain or a human review.
New exact-source build and review evidence is retained outside the package so
that recording outcomes does not mutate the tested source.

The historical `ArithmeticCertificate.lean` comment describing a future
soundness bridge predates `CertifiedLinear.lean`, which supplies that specific
finite-linear-algebra bridge. The original-covering, classification and
infinite-family proof boundaries must still be distinguished.

The official Linux release archive was independently downloaded from
https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2. Its SHA-256
`b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049`
matched the digest published on release asset 567981860. The binary distribution
is not included in this repository.

The source runner audits selected printed theorem closures. Its token and log
checks are practical safeguards, not an adversarial verifier or a substitute
for protected comparison, independent kernels and canonical rendering.

## New bridge port adaptations

The five new modules were first checked with Lean4.19.0. Their supported-version
port adds the same module visibility/exposure declarations, plus four local
tactic adaptations: a finite `decide` proof of residue membership, removal of
an `omega` invocation after simplification already closes its goal, explicit
unfolding of the normalized-column definition, and an explicit bounded-vector
equality before the upper-digit identity. These changes preserve all theorem
statements and mathematical definitions. Their independently reviewed hashes
are bound by `PORT-MANIFEST.json` and the new-bridge review.
