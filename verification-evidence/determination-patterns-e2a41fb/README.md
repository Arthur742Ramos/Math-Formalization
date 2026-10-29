# Local canonical Rules-component verification

This is a sanitized derivative of a local canonical preflight of the Rules
component at source commit `e2a41fb46531b444d4a104ea9bc4d277e06d9dc3`. It
selects the admissibility and relevance of the explicit status mechanism.
It does not establish the complete exact-pattern theorem or cover the paper.

The local run used the unmodified pinned Palomar submission pipeline
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. The source was fetched from the
public repository at the exact commit. Its three stages completed and the
report recorded a pass. This local run did not submit to, and provides no
acceptance from, the registry.

[`canonical-rules.json`](canonical-rules.json) records the checked hashes,
selected declarations, permitted axioms and restricted log tail. It omits
local paths and the raw report, which remain private. The original report
and receipt hashes are recorded, but those hashes alone do not let a reader
reconstruct or independently verify the local run. Reproducible results
require rerunning the pinned pipeline on the exact source and configuration.

Prior local validation evidence reviewed by an independent internal AI reviewer
for the unchanged Lean source at its preceding commit is available [on the earlier evidence branch](https://github.com/Arthur742Ramos/Math-Formalization/tree/a5fe0313597d2e057bafe0d0442a4196cafd6aa1/verification-evidence/determination-patterns-8fcd0b9).
The broader imported-definition inventory, visual inspection, remaining component
checks and final release review remain outstanding.

## Extrema component

[`canonical-extrema.json`](canonical-extrema.json) records the separate local
canonical pass for `witness_extrema_of_admissible` at the same source commit.
It assumes admissibility of the specified mechanism; it does not itself prove
admissibility, relevance, necessity or the full pattern equivalence. The
Challenge was 369 lines and 15,401 bytes. The report warns that the preferred
300-line review surface is exceeded; the preferred 32 KiB byte threshold was
not exceeded. This warning remains open for substantive editorial review.

For the Rules and extrema replays, con-ron reported acceptance of 528 and 536
declarations respectively. In both, it reported one `Lean.Syntax` inductive
block modeled in-process, with 30 generated records checked by the fold rather
than counted as file records.
This is a local preflight, with the same evidence and registry limits above.
