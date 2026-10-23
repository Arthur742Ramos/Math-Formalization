# Verification procedure and evidence scopes

The six selected contracts and every supporting theorem are free of holes
and new mathematical axioms. The approved standard axiom allowlist is
`propext`, `Classical.choice`, `Quot.sound`. AxiomAudit prints transitive
closures for eighteen substantive declarations.

Challenge and proof have equal bytes and only pinned Mathlib imports;
Solution imports the proof. Both contract entrypoints compile independently.
ChallengeTests and SemanticTests check the material meanings, the derived
order topology, the existing usual rational topology and examples `ℚ × ℚ`,
Empty and Unit. Imported definitions have exact source and excerpt hashes;
`../../scripts/check_imported_definitions.py --dependency-root` authenticates
them against clean pinned Git sources. Hash consistency does not establish
inventory completeness or mathematical fidelity; independent review has its
own explicitly scoped receipt.

Native checks compile a protected copy under a fresh module name, export
it and the candidate separately, and use the unmodified pinned
`Lake.Check.compareAt` and `checkAxioms` on all selected names, standard
axioms and all 26 primitive constants. Negative controls change the fixed
clopen-basis and address definitions and must be rejected. Kernel replays
consume the exported solution closure through Lean's kernel, NanoDa and
verified con-ron. These native checks have different isolation/resource
properties from Palomar's canonical full workflow and do not replace it.

Every outcome must bind the actual tested commit, package tree, source,
metadata/configuration/lockfile hashes, exact toolchain/dependency pins,
commands, logs and artifacts in an external immutable record. Later changes
require affected consistency checks and fresh review. A status-only source
must not inherit a predecessor's exact-source run.

Canonical full verification and rendering are separate gates requiring
specific authorization before launch. The release-packet guard must bind the
exact source and original full report before verified intake fields are
handed off. Browser visual inspection, editorial review, submission and
permanent registration are distinct facts. This source asserts no authority
to perform registry, credential, security-setting, merge or paid operations.
