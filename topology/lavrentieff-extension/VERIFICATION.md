# Verification procedure and limits

The eight selected theorem contracts and two fixed local domain definitions have
no holes or new axioms. `AxiomAudit.lean` prints their transitive axiom closures.
`LEChallenge.lean` equals the proof byte-for-byte and is compiled independently;
Solution imports the proof. ChallengeTests and SemanticTests independently check
the principal contract, Gδ/closure meanings, subspace topology, filter convergence,
complete-metric compatibility and empty-domain edge cases.

Retained imported definitions include exact upstream source and excerpt hashes,
Git object provenance and attribution. Run the root `check_imported_definitions.py`
with `--dependency-root` to authenticate the pinned clean checkout. Consistency and
build checks do not establish semantic inventory completeness; independent review
must cover that separately.

The native procedure compiles a fresh protected Challenge copy, exports it and the
Solution closure independently, then invokes the pinned unmodified Lake comparison
and axiom auditor. Two controls change fixed local domain-definition values and must
be rejected. Lean's kernel, NanoDa and verified con-ron replay only the exported closure.
These checks have different isolation/resource properties from canonical full
sandbox verification and do not replace it. Canonical full verification and Challenge
rendering are separate gates. No protected installer, new security permission,
registry intake or legal agreement is authorized by this document.

Lessons preserved from prior verification failures: use package-owned exact pins;
check Challenge names and dependency values, not just Solution elaboration; audit
actual transitive axioms; require negative controls to fail for the intended reason;
never infer passing edited bytes from predecessor receipts; distinguish native,
canonical, rendering, visual, editorial and registration outcomes. Record evidence
outside frozen source to avoid a self-referential status-edit/verification loop.
The source never describes a gate as passed without its own immutable receipt.

External receipts must bind exact commit/package tree, toolchain and lockfile,
Comparator/metadata/proof hashes, commands, logs, source archive and actual outcomes.
A verified intake handoff additionally requires canonical full/render evidence,
independent release-packet review and the root release-packet guard. Registry
submission waits for all gates and parent coordination; no submission is made here.
