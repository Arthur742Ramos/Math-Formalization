# Verification record

The complete proof module passed local Lean 4.35.0-rc2 elaboration against the
installed cache pinned to canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` on 2026-10-09.
The proof-closure axiom report is `verification/local-axioms.txt`.
All seven selected declarations and the Hausdorff/paracompact witness lemmas
use only `propext`, `Classical.choice`, and `Quot.sound`.
No textual theorem hole or custom axiom occurs in the package sources.

The transparent Challenge is byte-identical to the proof module and is compiled
separately. It imports only canonical Mathlib. The Solution publicly imports the
proof module and the axiom audit imports Solution. The local resource limits are
two threads and 3072 MiB per Lean process.

Local elaboration and the axiom report do not claim hosted verification.
Hosted mechanical preflight must be evidenced on the exact published commit. The dedicated workflow calls the pinned
PalomarSubmission reusable verifier at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` in `full` mode with
`palomar-standard-v1`. The verifier's workflow-call route has no registry state
or registry credentials and is predictive only. It is not a registry submission.
The draft PR records the actual run URL, exact checked commit and stage results
after the run completes; this immutable source snapshot makes no advance claim.

No default-branch merge or registry submission is authorized by this record.

Publication access history: the connector create-tree attempt returned HTTP 403, and sandboxed GitHub CLI initialization could not read its ordinary configuration. The supported require_escalated execution approval was subsequently granted for ordinary CLI status and repository-rights queries. Those checks verified Arthur742Ramos as the active account and push rights for this public monorepo. No credential, scope, configuration path or security setting was changed. Publication and hosted verification use the same approval-governed execution route.
