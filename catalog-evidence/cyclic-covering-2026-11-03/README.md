# Cyclic-covering source-publication evidence

This is source-bound **native verification and internal AI review**, not a
Palomar full verification, independent-kernel attestation, or registry receipt.
The tested source commit is `9baa98e9ab3e4ec8ae4963f44dacc7512a10b88b`,
and its package tree is `eb69e561a549e1c66586584df02750fd8ad6defa`.
This evidence is deliberately outside the frozen mathematical package.

## Successful checks

- `native/port-verification.json`: all 48 original modules compiled freshly with
  Lean 4.35.0-rc2, one worker, 517.847 seconds.
- `native/closure-report.json`: all 33 modules in the final theorem dependency
  closure, including the five new bridge modules, compiled freshly with the
  same pinned Lean, 246.846 seconds. Together these reports cover all 53
  implementation modules. This is two overlapping clean runs, not one 53-module
  run. Source and compiler-log hashes are retained; logs are in `native/logs`.
- `challenge/local-verification.json`: the exact standalone Challenge compiled
  with the pinned Lean. Its historical publication-status field records its
  state at the time of this check, not subsequent branch publication.
- `solution-receipt.json`: the exact Solution entrypoint compiled successfully
  against the already checked 33-module output. This is not a fresh dependency
  rebuild. The empty compiler log is accompanied by explicit exit-code evidence.
- `catalog/receipt.json`: all eight root validation stages passed on the exact
  tested source, including 402 regression tests. This is repository consistency
  validation, not proof verification.
- `PUBLICATION-PATCH-REVIEW.md`: independent internal AI review of the exact
  source, literal-data fidelity, declaration extraction, evidence and scope.
  It is not human or external peer review.

## Preserved failures and remaining gates

`attempts/catalog-1` and `attempts/catalog-2`, and the earlier regression log,
record missing historical Git objects. Read-only fetching the original commits
resolved those errors; no validator was weakened. `attempts/original-48-lean419`
retains the earlier 4.19 attempt: 46 modules passed and TriangleBatch04/06 were
killed by signal 9 with empty output. The cause is not established. The complete
supported-version run above subsequently passed all 48 ported modules.

`capacity.log` records an initial capacity CLI invocation that lacked its
prepared report. `standalone-host-capacity.json` then records the unmodified
pinned official capacity helper's actual findings. The host's 10,451,439,616
memory bytes are below the standard 15,032,385,536 minimum; the Namespace
profile also requires 16 CPUs versus nine available. These are standalone
capacity observations, not a prepared or completed canonical run. The official
pipeline pin is `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.

Finalized attribution, protected Comparator and dependency-value checks,
independent kernels, canonical full verification and separate Challenge
rendering remain outstanding. The source proves nonextension of 17 supplied
representatives, not exhaustive classification or unrestricted 10-by-6
nonexistence. No intake, registration, merge readiness or novel-priority claim
is made.

The recorded paths identify build artifacts on the execution host. They are not
required installation paths. `manifest.json` binds every evidence file except
itself; the package source is additionally bound by its Git tree and input
hashes in the native reports.

## Local history and publication transport

`source-history.bundle` preserves the four original locally verified commits,
through `52cf0bf6f0e4a9324192dd18f1b7eef31eaf1aa6`, including the tested source
`9baa98e9ab3e4ec8ae4963f44dacc7512a10b88b`. It requires the repository's existing
base `ab30c275aa3a76d390403a491c386d06ab131037`. Standard `git bundle verify`
checks its recovery prerequisite. The bundle is source/history only, without
credentials or compiler binaries.

The connected GitHub publication API creates a new commit identity rather than
reproducing local author/timestamp metadata. Original evidence continues to bind
the original commits and package tree. Publication uses unchanged source bytes;
final root checks and independent review distinguish the actual publication
commit from this retained native-build history.
