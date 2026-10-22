# Reproducible verification boundaries

Run from this package with the pinned Lean toolchain and locked dependencies:

```sh
lake build
python3 scripts/check_package.py
python3 ../../scripts/check_imported_definitions.py \
  --project-path game-theory/sparse-equilibrium-completion \
  --dependency-root .lake/packages/mathlib
```

After committing the complete source, run
`python3 scripts/verify_native.py --out /absolute/path/outside/the/package`.
The verifier refuses a dirty package, removes only package build artifacts,
retains dependency caches, and rebuilds the default targets at that commit.
Its external receipt binds the Git commit/package tree, file hashes, Comparator
config, exact native toolchain, locked Mathlib source, commands, logs and exports.

The native verification sequence builds both independent contracts, all actual
axiom reports, the definition bridges through each entrypoint, and a semantic
counterexample proving that cuts cannot replace omitted-row guards. The protected
Challenge is a deterministic assembly of the exact five local source bodies with
full proofs, zero definition holes, and exposed public declarations; it is
compiled under a different module alias
without importing the solution. The unchanged pinned `Lake.Check.compareAt` API
compares dependency identities. A modified fixed `envelope` definition must be
rejected. `Lake.Check.checkAxioms`, native module checking and independent checking
of the solution export provide separately logged checks. No custom comparison
normalization is introduced.

`scripts/assemble_challenge.py --check` authenticates this assembly. Source module
imports are replaced by their fixed bodies; external Mathlib imports are retained.
The immutable first foundation checkpoint remains tagged separately with its own
exact-source receipt; later development never inherits that receipt automatically.

These native checks do not constitute the registry's canonical Linux sandbox,
renderer, editorial decision or publication. They do not prove correspondence
with the manuscript or whole-paper coverage. Independent source/semantic review
and the explicit scope map address those separate questions. Exact-source
receipts and final reviews are retained outside the frozen source to avoid a
self-referential verification/status edit loop.

Before an eventual release, complete the outstanding mathematics in SCOPE.md,
confirm project-specific human roles, recheck current intake policy/schema and
account/duplicate state, obtain exact-source canonical and rendering receipts,
and run the repository release-packet guard. A security-changing runner requires
specific action-time authorization. No prior topology-job runner approval or
submission authorization transfers to this project.
