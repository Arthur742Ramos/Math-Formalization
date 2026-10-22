# Verification procedure and boundaries

The protected Challenge and proof source must have identical bytes, use the
module system and depend only on pinned Mathlib imports. Solution imports the
proof source. Eleven theorem targets are selected; no definition holes or new
axioms are permitted. Each target's complete transitive axiom dependency list
is checked against `propext`, `Quot.sound` and `Classical.choice`.

Native verification compiles a fresh protected module alias and the candidate
separately, exports both closures and applies the unmodified pinned
`Lake.Check.compareAt`, `checkAxioms` and all26primitive targets. Negative
controls must reject independently altered fixed address functions and the
clopen-basis predicate. Lean's kernel, NanoDa and verified con-ron replay the
solution export. These checks do not weaken or replace Palomar's canonical
protected-source and resource-bound workflow.

SemanticTests and ChallengeTests separately import Solution and Challenge.
They connect literal pinned definitions with the mathematical meanings,
exercise the full iff, and retain empty-space and isolated-singleton negative
examples. Retained definition and source hashes are consistency evidence;
separate independent review establishes inventory completeness and semantic
fidelity, while actual Lean builds establish elaboration.

The final external release record must identify the frozen source commit,
package tree, metadata/config/lockfile hashes, native logs and exact-source
canonical full and renderer reports. Original reports and workflow provenance
must be inspected independently. `scripts/check_release_packet.py` is the
strict final guard; its status-only mode is not a verified handoff. Rendering
success and browser visual inspection are separate observations.

Each run's outcome is recorded as immutable evidence outside the frozen
source package. Do not infer a later source passed an earlier run. No public
entry, acceptance, registry submission, merge authority or new disposable
runner security exception is asserted by these source instructions.

## Completed native checkpoint

The restored proof and Challenge bytes passed exact-toolchain compilation.
Both semantic bridge modules compiled separately. Protected native comparison
passed all eleven targets, the axiom check and all26primitive targets; altered
`BinaryScheme.code`, `HasClopenBasis` and `BinaryScheme.next` bodies were each
rejected. Lean, NanoDa and verified con-ron accepted the solution export;
verified con-ron accepted14,096 declarations. The retained inventory was
authenticated against30exact pinned Mathlib files, and all189repository
regressions passed. These observations are native checks, not the canonical
full/render gate. Exact hashes, commands, source commit and logs are retained
in immutable external evidence. Canonical results must independently bind
the frozen source before a ready-to-submit handoff.
