# Completed canonical verification and proposed submission packet

Frozen submission source: `d33817461fadbe8d7498a237b0c5bc27dc044afb`,
project `topology/sierpinski-rationals`. The caller/evidence commits are distinct
from this exact verified mathematical source. All 24 package files match tree
`e54c3b7a138aa6386c73c23ae3b349c97351be5f`.

- [Full run 39882986575](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39882986575): success, attempt 1; original [full-report.json](full-report.json) SHA256 `66ac793f2a013d39cba252bbfd248e4ff8842dea0bec7a88dd739273eb11e368`.
- [Render run 39882986107](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39882986107): success, attempt 1; original [render-report.json](render-report.json) SHA256 `59049f981d2a08f5cf649c9e8375d391bc63d0743a55d43db7b19b98f9a199b5`.
- Renderer artifact tree SHA256 `df209c86a065e04a3589fb4e831ccea0a89f8f3058ae3a97ccce152b8897fb80`; all 13 manifest-covered files plus the manifest (14 files total) are preserved in the [original rendering artifact ZIP](render-artifact.zip), including `Challenge/index.html`. This preservation is not a claim of browser visual inspection.
- The [strict proposed packet](submission-packet.json), [exact-source archive](sierpinski-rationals-d338174-source.tar), [file inventory](source-identity.json) and [release guard receipt](release-packet-guard.json) agree. Archive SHA256 `5591b5eec8a7f8207f52ed85a3553d917a3174f1ce6a0d3639a42ef03c3d899e`.

Protected comparison accepts all six selected contracts under only `propext`,
`Quot.sound`, `Classical.choice`. Lean and NanoDa accepted the exported closure.
Pinned policy replays verified con-ron separately after the mandatory comparison;
it accepted 18,207 declarations, with its informational in-process Lean.Syntax
model diagnostic retained in the original report. The release guard now handles
that protocol while preserving its historical protocol and requiring all three
acceptances for this packet. Its 42 tests cover altered source/metadata/archive,
missing or duplicate kernels, unverified commands, declines, rejected/ambiguous
verdicts and wrong checker provenance. This guard change is outside the frozen
mathematical package.

[Independent artifact authentication](independent-canonical-authentication.json)
checks provider ZIP digests, original report-byte and log bindings, exact source
and dependency pins, and the rendered six-declaration surface and 13-file manifest tree.
Both run APIs and original job logs are retained alongside the reports. The
canonical warning about the preferred 300-line review surface is preserved;
the 493-line Challenge remains below the hard 1,000-line/100-KiB limits.

The [authorization/run ledger](authorization-and-run-ledger.json) records one
approved pair and conditional narrow bubblewrap AppArmor setup on disposable
runners. An initial manual-dispatch HTTP404 created no run; branch/path-scoped
push triggers launched the pair without changing the pinned job bodies or source
selectors. Approval is consumed: no repeat run, registry intake, credential
creation, registration or merge is authorized.

The packet is prepared for review, not submitted. Bounded duplicate searches
found no match; exhaustive registry-wide search and current private service
state remain unconfirmed. Internal AI review is distinct from human/external
review, editorial acceptance and public registration. Historical pending/zero
fields in the preceding native checkpoint are dated observations before this
approved pair.
