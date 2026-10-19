# Source-bound verification protocol

Use the selected package’s committed lean-toolchain, lakefile.toml and
lake-manifest.json through /workspace/palomar-tools/run in the cloud environment.
ELAN_HOME is /workspace/palomar-tools/elan and MATHLIB_CACHE_DIR is
/workspace/palomar-tools/mathlib-cache. The wrapper preserves inherited PATH,
arguments and exit status. All nine Git dependency pins are retained.

The local six-module build checks full proofs, independent Challenge/Solution
contracts and semantic boundaries. AxiomAudit.lean prints actual transitive
closures for all seven selected theorems and both selected definitions.
verification/local-axioms.txt records those closures. scripts/check_package.py
checks pins, metadata, roles, sources, entrypoints and the frozen manifest; it
parses a supplied fresh axiom log and never substitutes an expected allowlist
for observed output. It performs no build or registry operation itself.

An exact-source canonical full report must bind source commit, metadata,
Comparator, Challenge/Solution, lockfile, selected declarations, protected
provenance and actual kernel acceptance. Rendering and actual artifact/visual
inspection are separate evidence. The root release-packet guard must validate
the exact proposed source/report/archive before a verified handoff. Any later
metadata or source change needs its own affected checks and independent review.
Outcomes belong in external immutable receipts, avoiding a self-referential
status-edit/verification loop. Local proof compilation alone does not certify
protected full comparison, independent kernels, rendering or service outcomes.

The cloud user-namespace UID map is read-only; do not bypass it to run Comparator.
A pinned runner installer can conditionally load a temporary AppArmor policy.
That security operation requires new specific approval for each fresh run;
approvals for previous projects or attempts do not transfer. Prepared callers
must stay undispatched until the exact required approval is supplied.
No authentication, proof tag/gist, service intake, editorial decision or
registration is implied by this source package. Existing attempts and current
protocol/capability must be reconciled separately before any service action.
