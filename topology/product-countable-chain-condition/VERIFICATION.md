# Verification and provenance

The six selected theorems and two selected literal definitions are listed in
`comparator.json`. Proof/Challenge use identical source bytes and independently
elaborate; Solution imports only ProductCCC. Both entrypoint test files check
literal definition values. `AxiomAudit.lean` emits actual transitive closures
for all eight names; the checker requires exactly those names and the approved
standard axioms propext, Classical.choice and Quot.sound. No custom axioms or
proof holes are permitted. The complete frozen file manifest excludes only itself.

Local preparation uses the package-owned Lean v4.35.0-rc2 toolchain and nine locked
Git dependencies, including Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Only the package name differs from the previous package's lockfile header;
all dependency records are preserved. Cached dependency objects may be shared;
the project's proof, Challenge, Solution, contracts and semantic tests compile
in this independent package. This does not attest a cache-free rebuild.

Ordinary local/hosted Lean build, transitive axiom audit, package consistency,
independent source fidelity and implementation review, protected Comparator,
independent kernels, canonical rendering, browser visual review, editorial
review and registration are different stages. A stage is completed only when
its own preserved evidence identifies the exact tested source. A source-tree
comparison to another checked commit is not a fresh check of that commit.

The metadata schema is checked against the last inspected pinned v0.4 submission
contract, not represented as a fresh reading of unavailable current service
policy. Service capability, current protocol/limits, duplicate/private attempts
and public existing ID must be reconciled before any intake. This package does
not grant service actions or runner security changes. Evidence and external
receipts must preserve any future outcomes without creating a source-status loop.
