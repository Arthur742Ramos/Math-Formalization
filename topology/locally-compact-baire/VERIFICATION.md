# Source-bound verification

Use this selected package's committed lean-toolchain, lakefile.toml and
lake-manifest.json. All nine Git dependency pins are retained. The local
six-module build checks full proofs, independent Challenge/Solution contracts
and semantic boundaries. AxiomAudit.lean prints actual transitive closures for
all six selected theorems; verification/local-axioms.txt records those closures.
The observed closures use only propext, Classical.choice and Quot.sound.

Run `lake build`, then `lake env lean AxiomAudit.lean` for fresh local evidence.
`scripts/check_package.py` checks pins, metadata, author and maintainer roles,
sources, entrypoints and the frozen manifest. It parses a supplied fresh axiom
log and never substitutes an expected allowlist for observed output. It performs
no build or registry operation itself.

An exact-source canonical full report must bind the source commit, metadata,
Comparator, Challenge/Solution, lockfile, selected declarations, protected
provenance and actual kernel acceptance. Rendering and actual artifact/visual
inspection are separate evidence. The repository release-packet guard must
validate the exact proposed source/report/archive before a verified handoff.
Any later metadata or source change needs affected checks and independent review.
Outcomes belong in external immutable receipts, avoiding a self-referential
status-edit/verification loop. Local compilation alone does not certify protected
full comparison, independent kernels, rendering, editorial decisions or service
outcomes. Current authorization and actual intake state are separate prerequisites
before any service action; no registry outcome is inferred from this package.

The material imported-definition manifest uses schema2 to distinguish literal
definitions from class-field and proved-equivalence bridges. Run the repository's
scripts/check_imported_definitions.py for static consistency, then its
--dependency-root mode against the already available exact clean Mathlib checkout
for source provenance. Both entrypoint test modules compile the documented
hypothesis and conclusion meanings plus the proof-critical compactness chain.
Neither checker establishes inventory completeness, editorial significance or
service clearance; independent exact-source review remains required.
