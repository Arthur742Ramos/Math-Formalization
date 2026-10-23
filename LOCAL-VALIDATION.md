# Local validation

All necessary validation runs locally before merge or verified handoff. Root
AGENTS.md defines the gates. Repository Actions are retired; do not restore them
from an incoming branch. Existing hosted reports remain evidence of their exact
historical source only. Palomar's own intake checks remain separate and mandatory.

## Migration inventory

At main `6c922670eeea8bf2f4908fc944510f3512ef3f9f`, all 56 root workflow
definitions were validation CI: 20 native Lean/package workflows, one catalog
workflow, 19 canonical full preflights and 16 Challenge renderers. After this
change `.github/workflows` has no definitions. No release, deployment or security
automation was found or removed. No settings, protections or existing jobs change.

[The inventory](validation/workflow-inventory.json) lists every filename, source
hash, class and replacement. [Retired definitions](validation/retired-workflows)
preserve their exact bytes, pinned pipeline revisions, inputs, shell commands,
setup assumptions, resource profiles and artifact expectations. They are inert
historical references outside `.github`, not an executable Actions configuration.
Do not execute their hosted setup, cleanup, sudo or sandbox installers locally.

The five open heads audited before editing were PR43 `a17446dd0196fd1192e3a6dc3c12b22d7a9e3ac2`,
PR40 `ba4281cef86cbe6946478c926c03f22ffc52a83d`, PR39
`67f0657bce5da9a6405edd63b6d8b8243ec61f4c`, PR37
`f0db63b40fa4fe3aa6292be3c656687fa0e44d16` and PR36
`7ff901d68c9e248040215d0251f76c301ad52051`. Each had only root AGENTS.md,
identical to main's prior policy. Their workflow counts were 57, 56, 57, 56 and
55 respectively. Reconcile their CI files before those branches merge; this
patch does not edit those branches or their mathematical packages.

## Root checks and native packages

Use a clean committed checkout as a non-root owner. Python 3 and Bash are needed;
the migration tests also use PyYAML. Install prerequisites separately under the
authorized environment policy. No root project scripts are permitted. In the
campaign environment use Ubuntu-24.04 WSL as `formalization`, your own checkout,
preinstalled Elan 4.2.4, and each package's exact Lean/dependency pins. The existing
paper, hodge and pr43 workspaces belong to other owners.

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 scripts/local_validate.py catalog --seconds 600
python3 scripts/local_validate.py banach-mazur-category-lean.yml --plan
python3 scripts/local_validate.py banach-mazur-category-lean.yml --seconds 1500
```

The runner acquires `/home/formalization/workloads/.heavy-verification.lock`
without waiting. A busy lock is a coordination blocker, not permission to run
concurrently. It bounds the entire command sequence, terminates timed-out process
groups, fails on any failed command or source mutation, and retains logs and a
commit/tree-bound receipt under `.git/local-validation/run-*`, outside the
committed source. Preserve and hash that receipt and logs in durable external
evidence before deleting a checkout. Do not edit tested package prose to report
success; link the external receipt in the handoff. A receipt is evidence, not an
independent review or an attestation of the host's security.

`catalog` executes the full root catalog/package checks, all root regression
tests, the five retained material-definition checks and the historical
collectionwise release-packet check. These are consistency and regression gates;
recorded axiom logs consumed by them are historical input, not fresh axiom runs.
The Smirnov and perfect-image frozen validators require historical workflow
fixtures. The catalog runner checks their unchanged package trees against their
frozen records, then executes the unchanged validators in disposable local
copies with byte-identical retired fixtures. No active workflow is restored.

Native plans retain every validation `run` command from their original native
workflow. The only changes are replacing tool installation with a preinstalled
exact-toolchain check and omitting hosted Actions setup/upload steps. Commands
retain package cwd, scoped caches, imported-definition/source authentication,
Lean/core hashes, fresh builds, semantic entrypoints, axiom checks, definition
negative controls, and any package-specific leanchecker checks. Authenticated
cache reuse must be recorded as reuse. Add package checks for new packages or
new requirements; the retired inventory is a coverage floor, not a forever-fixed
validation specification. Root policy-only edits do not require rebuilding
unchanged mathematical packages or claiming fresh canonical results for them.
Native execution refuses existing package `.lake/build` outputs or loose Lean
compiled artifacts; prepare a fresh owned checkout for a new run. Do not delete
or reuse another owner's build tree. Dependency cache authentication remains a
separate gate.

## Canonical full verification and rendering

A native Lake build does not replace canonical protected comparison, source
provenance, compiler and independent-kernel checks, confinement controls, fixed
definition rejection controls, or Challenge rendering. For affected mathematical
packages run the complete pinned canonical verifier and renderer locally, with
their supported profile, dependencies and authenticated tool binaries. Review
the exact pinned pipeline implementation and current intake requirements first.
The retired definitions retain the original per-package revision and inputs;
historical fixed source SHAs are not substitutes for the new source being checked.
If a required profile, sandbox or tool is unavailable, retain the failed receipt
and report the gate blocked. Do not change security settings or weaken checks.

The following wrappers require an already available, clean, independently
authenticated pipeline checkout. They neither clone another repository nor
install tools, change profiles, use sudo, dispatch a workflow or submit to a
registry. Supply an existing authenticated bubblewrap v0.12.0 executable and
the installed licensee/Ruby, Python, Lean and kernel dependencies expected by
the pinned pipeline. Use a non-root virtual environment outside pipeline source.

```sh
python3 scripts/local_canonical.py full \
  --pipeline /approved/existing/pipeline --pipeline-commit FULL_REVIEWED_SHA \
  --inputs /external/evidence/full-inputs.json --bwrap /approved/bin/bwrap \
  --evidence-root /external/evidence --seconds 7200
python3 scripts/local_canonical.py render \
  --pipeline /approved/existing/pipeline --pipeline-commit FULL_REVIEWED_SHA \
  --inputs /external/evidence/render-inputs.json --bwrap /approved/bin/bwrap \
  --evidence-root /external/evidence --seconds 7200
```

`full-inputs.json` is the canonical event object `{"inputs": {...}}`, containing
repository `Arthur742Ramos/Math-Formalization`, the exact new 40-character
`commit`, `pipeline_commit`, unique `request_id`, `mode: "full"`,
`execution_profile: "palomar-standard-v1"`, and the package's `options` JSON
string with project/comparator/metadata paths and the accurate authorized
relationship. Use the archived job inputs as a schema reference, not as proof
of authorization or as the source SHA for a new check.

`render-inputs.json` contains exactly the canonical prepare fields:
`repository`, `commit`, `challenge_sha256`, `project_path`, `challenge_path`,
`solution_path`, `comparator_config_path`, `lakefile_path`, and
`lean_toolchain_path`. Hash the exact Challenge bytes at that commit and use
repository-relative paths. The wrapper invokes canonical prepare and execute;
the full route also invokes the capacity gate. It uses the same shared lock,
a fresh evidence directory, bounded process groups and exact-source reports.
The report's workflow URL is an honest local evidence URI, never an invented
hosted run. Pin/profile and tool authentication still require independent review.

Inspect report status and every required stage, kernels, negative controls,
rendered source/bundle hashes and resource receipt. Inspect the sanitized
rendering visually. A process exit code of zero alone is insufficient; wrappers
require a passing canonical report as well. Reconcile any canonical-version
interface change explicitly before execution; do not patch canonical safeguards.
The wrappers are local preflight adapters, not registry intake clients.
If Palomar's current external protocol requires a hosted reusable-workflow
receipt, a local CLI pass does not satisfy that external prerequisite. Report
the protocol incompatibility as an intake blocker under the local-only direction;
do not launch a hosted replacement, invent a hosted URL or claim the gate passed.

## Final gates and receipt review

Run independent patch review and, for mathematical changes, independent source
fidelity, definition-inventory and mathematical-scope review. Bind review to the
exact final source, config/metadata/pins, report and artifact hashes, noting
human versus internal AI review. Preserve failed attempts and negative controls.
Never relabel reused files or predecessor receipts as newly executed checks.

For a verified handoff, run `scripts/check_release_packet.py` with the exact
packet and exact-source full report and independently review its receipt. Check
current metadata/schema, licensing, roles, provenance and packaging requirements.
Do not conflate machine success with Palomar editorial acceptance.

Before merge, read current required contexts and effective branch rules. If
deleted CI contexts are required, report their exact names/configuration and
stop. Do not manufacture statuses, bypass a protection or change settings.
After merge prove the merged package/source tree equals the reviewed tree;
label that equality as carried-forward evidence, not a fresh post-merge check.
