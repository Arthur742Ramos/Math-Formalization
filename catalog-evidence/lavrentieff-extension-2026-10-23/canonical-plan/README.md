# PR43 inert exact-source canonical plan

This is a reviewed proposal for parent coordination, not approval or a verification
receipt. No workflow is installed under `.github/workflows`; no installer, hosted
run, rendering, security change, merge or registry intake is performed by this plan.
The parent will coordinate one bundled approval. Do not ask the user separately.
This plan concerns only PR43 and does not modify another target.

## Frozen identities and status audit

- Repository: `Arthur742Ramos/Math-Formalization`, PR43.
- Source: `e2d111be48a52d4e3dd803b7b77a72b31cd59ca7`.
- Project: `topology/lavrentieff-extension`; package tree
  `7b387d9479cd6b5bf8427e8f085f46c64a776f11`.
- Pipeline: `PalomarRegistry/PalomarSubmission` at
  `ad5db9e7ff8b17523d73aeb244aaeabcde810c64`, unmodified.
- Lean: `leanprover/lean4:v4.35.0-rc2`, compiler commit
  `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- Verso: `9f8096e40b31715b1d8d5997f15a0bd832f7e37d`, the currently resolved
  v4.35.0-rc2 release. Renderer preparation must resolve this same commit before
  any renderer installer runs; dependency drift stops the plan.

`plan.json` fixes all20 source-file hashes, the package Git tree, a256000-byte
Git project archive (`bbddf0303f9b9b9221002b0c342605ba7124e2a930580c508436f99b96d4fe5c`),
selected contracts, pins and retained pipeline-file hashes. Source status audit
found no contradictory source-contained 'canonical not run' claim. Source wording
requires external receipts and never promotes native checks to canonical checks.
No source edit is required to record future success. All native receipts retain
their historical scope. There are eight selected theorem targets and no definition holes.

## One conditional pair, only after approval

`canonical-pair.yml.inert` is outside `.github/workflows` and has no operational
trigger here. After specific parent-coordinated approval, the parent may copy its
identical bytes once to `.github/workflows/palomar-lavrentieff-pair.yml` on
`topology/lavrentieff-extension` and push that activation commit once. The exact
activation workflow commit and file hash must be retained separately from the
frozen source commit. Do not combine that activation with any source-package edit.

The proposal permits exactly ONE canonical-pair workflow run, ONE full mechanical verification,
and at most ONE renderer, sequentially. The renderer is conditional on both the
reusable full job succeeding and an authenticated original same-run full report.
There are three caller job nodes: full, authenticate, render. The reusable full
node expands to profile plus verify, so the canonical pair starts at most FOUR
physical jobs. The activation push also synchronizes PR43, whose unchanged Project
catalog workflow matches this PR's existing catalog/source diff: allow ONE ancillary
catalog workflow run with ONE ten-minute static-check job. The total activation
budget is therefore at most TWO workflow runs and FIVE physical jobs, of which
only verify and render are protected build jobs on their own fresh disposable runners.
The ancillary catalog check has no installer or canonical build; its protections
and trigger remain unchanged. No additional automatic workflow was found in the
current repository trigger audit.
The upstream profile job is a short trusted resolver with no candidate build;
it has no explicit timeout in the pinned workflow and inherits platform defaults.
The authentication job is limited to10minutes. No automatic verification rerun,
retry, alternate source, profile upgrade or new intake is permitted. The pinned
full job may retry uploading its bounded report up to three times; these are
artifact uploads, not repeated verification executions. `github.run_attempt != 1`
skips the full/authentication/render jobs. A second activation push or fresh run
requires fresh parent coordination; concurrency queues, rather than authorizes, runs.

The full report gate checks actual status/pass and completed full phase, same
workflow URL/request, source commit and project, actual package Git tree and all
source bytes, Comparator/metadata/lockfile/Challenge/Solution hashes, exact toolchain
and Mathlib pin, selected names/axioms, protected-configuration digest, independent
kernels, verified two-worker con-ron acceptance, standard profile and pipeline bytes.
It re-creates and authenticates the project archive. A successful GitHub conclusion
alone is insufficient. Any missing/failed/wrong-source report stops rendering.
The gate's synthetic tests exercise schema acceptance and20 wrong-evidence cases;
the fixtures are not canonical verification and grant no authorization.

## Runner and resource scope

Select `palomar-standard-v1` explicitly for both stages: GitHub-hosted disposable
Ubuntu24.04/x86_64. Never inherit the pipeline catalogue default, which selects
Namespace with a privileged-container feature. No paid capacity/profile change
or persistent/self-hosted runner is proposed.

Full verification uses the unchanged standard profile:350-minute job maximum,
19,800-second execution budget, at least15032385536 bytes (14GiB) effective RAM
and21474836480 bytes (20GiB) free workspace; memory.high95%, memory.max98%,
32,768 tasks,1,048,576 requested open files and1TiB phase-file size ceiling.
Actual applied limits and host capacity must be retained from original telemetry;
the implementation may clamp an rlimit to the host allowance. Full CPU use follows
the standard host; con-ron is fixed at two workers with a1,800-second replay limit.
No custom looser bounds or Namespace fallback is included.

Renderer job maximum is the pinned resolver's350+10=360minutes, covering setup
and phases. A read-only standard-profile capacity check runs on that actual renderer
runner before verifier-dependency, elan, Lean and bubblewrap installation, and
retains the observed RAM/CPU/free-disk report. Its unchanged confined build uses12GiB RAM,400% CPU quota (four CPUs),
512 tasks,4096 open files,2GiB individual build-file limit, and a21,600-second
build ceiling. HTML conversion has600seconds and sanitization120seconds; the
outer360-minute job remains the total renderer ceiling, so phase ceilings are
not additive guarantees. Cache-download and cache-tool helper bounds remain the
pinned upstream values. The render work cap is12GiB, cache8GiB, with the exact
smaller helper/archive caps retained in the unmodified renderer source.

Output caps stay8MiB (8,388,608bytes) PER FILE,25MiB total,2000 files and4000
filesystem nodes. No limit increase or output filtering is proposed. A bounded
size diagnostic records raw HTML sizes even if sanitization rejects an oversized
page; it never uploads the oversized raw page or changes the canonical verdict.

## Rendering size risk

The exact Challenge is218lines/10,535bytes. An authenticated prior same-pipeline,
same-toolchain Sierpiński render used493lines/22,051bytes and produced a
5,681,728-byte `Challenge/index.html`, below the8MiB cap. Its original zipped
HTML bytes and digest were rechecked without running a renderer.

Illustrative line/byte scaling gives approximately2.51–2.71million bytes here,
about30–32% of the cap. This is NOT a bound, rendering result or promise: inferred
types, tactics, metadata and hover data may expand differently. Static size risk
appears modest but remains unmeasured. This comparison supports keeping the
reviewed source unchanged for the single conditional attempt. Actual cap failure
must be recorded and stop the plan. Any subsequent presentation/source change
needs new source-bound review and fresh exact-source verification; do not relax
caps, hide declarations, reuse the old full pass for changed metadata, or auto-retry.
No other project's failure is diagnosed or repaired here.

## Exact security actions requiring bundled approval

On EACH of the two fresh protected-job runners, the unmodified pinned installer
builds checksum-pinned bubblewrap0.12.0 in `$RUNNER_TEMP/bwrap-bin`. The archive
SHA256 is9760d007363e3abba7c747489910f9f82d9fca53ba3bd3282e396fa3c97a3314.
It installs a0755 binary and, only where the kernel reports restricted unprivileged
user namespaces, writes `/etc/apparmor.d/palomar-bwrap` with sudo and loads it via
`sudo apparmor_parser -r`. The profile attaches to that exact temporary bwrap path,
uses `flags=(unconfined)` and grants `userns`. This conditional scoped profile
write/load is the explicit security exception to coordinate; it is not implied by
mathematical verification or merge authorization. The installer reads the sysctl;
it does not change its value. No global AppArmor disable, sysctl write, setuid
installer, firewall/credential-scope/billing change or persistent-host change is proposed.
`sudo apt-get` installs meson,ninja-build,libcap-dev,pkg-config on the disposable runner.

The pinned pipeline also obtains run-scoped cgroup delegation. On the intended
systemd host it uses `systemd-run --user --scope --property=Delegate=yes`.
Its built-in non-systemd fallback is `sudo -n` of the pinned cgroup_delegate.py:
it can move container-root processes to `palomar-host`, enable memory/pids/cpu
controllers, create/chown a fresh run subtree, then drop privileges. That conditional
root-helper footprint is disclosed for the parent's bundled decision; do not
substitute another helper, change the host to enable it, or launch a privileged
Namespace fallback if standard capacity/delegation fails. Both paths are confined
to a disposable runner and retain original bootstrap/resource telemetry.

This plan has executed NONE of these actions. If the bundled approval does not
cover the precise pinned security footprint, keep the plan inert. No independent
user permission request is made by this task.

## Future evidence and source-freeze policy

Retain original full/render reports, SHA256 digests, artifact API manifests and
archives, run ID/URL/attempt, activation workflow head/file hash, immutable reused
pipeline reference, exact source commit/tree/archive, metadata and configuration
hashes, package pins, resolved Verso and profile, tool digests, resource telemetry,
confinement diagnostics, kernel outcomes, HTML byte counts/hashes and manifest.
Independently authenticate these original artifacts, including page-size compliance;
retain warnings/failed stages honestly. Browser visual inspection, editorial review,
public registration and mechanical rendering remain separate facts.

After any outcome, add new evidence OUTSIDE the frozen package, preserve the dated
native/blocked checkpoint, and update root catalog/latest-results pointers with the
actual outcome. Explicitly prove the later PR/merge package tree equals the tested
source tree; never call that a fresh post-merge run. Do not edit the package README,
metadata, review/verification notes or hashes merely to record successful stages.
If any package byte must change, stop: the source/configuration identity changes,
and a fresh reviewed exact-source run is required before verified handoff.

Only after full and rendering pass, final independent receipt/packet review and
the source-bound release-packet guard may the parent consider readiness/merge
under existing conditional authorization. Registry submission remains separately
blocked pending parent coordination and duplicate-intake checks. This plan itself
performs neither action.

## Planning-only publication

If the reviewed inert proposal is published to this PR, use a `[skip ci]` commit
for these plan-only external files to honor the instruction to start no hosted
runs. Existing pending/required gates remain unsatisfied; this is not a gate
waiver or merge approval. The repository has no pull_request_target/workflow_run
trigger. A later specifically approved activation push must omit skip instructions
and may start only the one planned pair. No workflow is disabled or protection changed.
GitHub documents the pending-check behavior at
https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs.
