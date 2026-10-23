# Protected execution and rendering plan

No protected run is authorized by this document. The candidate source, selected
names, metadata, config and dependency pins must first be frozen and linked to
an exact local report. A later evidence-only commit must be distinguished from
that tested source. Existing continuation evidence remains immutable history.
This is a conditional algebraic package, not an analytic compact-Kähler result.

## Current observed execution blocker

The cloud's harmless namespace probe returned exit 1:

```
bwrap: setting up uid map: Read-only file system
```

The command was `bwrap --unshare-user --uid 0 --gid 0 --ro-bind / / --proc /proc
--dev /dev /bin/true`. No host security configuration was changed. Bubblewrap is
v0.12.0. The current executor has a 16 GiB cgroup memory limit, four CPU cores
and roughly 29 GiB free disk. Ordinary pinned Lean builds succeed here.

PalomarSubmission HEAD was rechecked as
`ad5db9e7ff8b17523d73aeb244aaeabcde810c64`; policy HEAD remains
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`. Its default Namespace profile needs
28 GiB minimum host memory and a privileged container. Its published
`palomar-standard-v1` alternative uses GitHub-hosted ubuntu-24.04, needs 14 GiB
minimum host memory and 20 GiB workspace free, and allows 19,800 seconds within
350 minutes. Memory fits the alternative here; namespace confinement does not.
No relaxation, host modification or substitute unsandboxed run is proposed.

## Exact approval required before protected execution

Approve **one** predictive full mechanical preflight of the exact candidate
source SHA and digests in the new package receipt, using the pinned pipeline
above and `palomar-standard-v1` on a disposable, already available standard
GitHub-hosted runner, only after zero-charge eligibility is confirmed. The reviewable caller is
[run-plans/protected-preflight.yml](run-plans/protected-preflight.yml), deliberately
outside `.github/workflows`. It is inert. After the source freeze, a separate
evidence artifact substitutes the exact source SHA for `APPROVED_SOURCE_SHA`;
that instantiated file, its SHA256 and this plan are the concrete approval
subject. After approval only, an operator can copy those exact bytes to
`.github/workflows/hodge-protected-one-run.yml` on the existing draft branch.
Its path-restricted push trigger starts one attempt without merging the draft
or requiring a workflow-dispatch entry on the default branch. Rerunning that
attempt requires fresh authorization; the caller rejects automatic reruns.
No workflow activation or dispatch is part of this preparation.

The approval must explicitly cover the 19,800-second verifier budget, the
350-minute verification-job limit, and the pipeline's
runner-local setup: pinned toolchain/bubblewrap installation, package-manager
build dependencies, sandbox namespaces and delegated cgroup supervision. It
covers no changes to the user's Mac or current host, no new credential, no paid
runner, no repository security-setting change, no new legal acceptance, no
submission and no registration. If a zero-cost permitted runner cannot be
confirmed, stop and report that limitation rather than provision one.

Public repository standard-runner minutes are free, but this does not establish
zero total cost. The pinned workflow uploads artifacts with 90-day retention
and uses dependency caches. Before activation, obtain a read-only account-level
storage/usage/quota assessment and bound artifact/cache use and retention
against the available free allowance for the complete retention period. The
current assessment does not establish that bound. Do not change billing,
retention/security settings or provision paid capacity to resolve it. If the
pinned workflow cannot ensure zero charges, the run remains blocked; a changed
workflow/pipeline requires a newly pinned, reviewed plan and exact approval.
See [GitHub Actions billing](https://docs.github.com/en/billing/concepts/product-billing/github-actions)
(observed at preparation). Deleting artifacts later does not cancel accrued
storage charges.

A fresh attempt needs fresh applicable authorization. Existing topology-run
approvals do not apply. No protected gate is marked passed from ordinary Lean,
syntax/type inspection, parser tests, or source hashes.

## What the canonical full run must prove

1. Fetch the exact public source and validate metadata/config/license, module
   headers and limits. Check Challenge size (995 lines, approximately 61 KiB at
   preparation) and retain its readability warning; the warning is not editorial
   approval. Verify the official pinned dependency closure.
2. Compile the Challenge independently against frozen canonical dependencies,
   under the unpredictable verifier-owned namespace. Audit every dependency
   source byte and prevent candidate output replacing that surface.
3. Run the pinned positive and ill-typed negative controls, including the
   confinement/write-boundary and kernel controls, before building this source.
4. Build the Solution in the canonical network-disabled sandbox, export both
   sides, then compare all selected theorem/definition names and permitted
   axioms using the protected configuration. Missing names, changed contracts,
   illegal axioms or proof/definition rejection must fail closed.
5. Require Lean and NanoDa acceptance. Attempt con-ron on the exact protected
   export within its published 30-minute advisory cap. Record an authenticated
   decline separately; never list a declined kernel as successful verification.
6. Preserve report, source/metadata/config/toolchain hashes, protected namespace,
   control results, accepted kernels and kernel attempts, run URL and artifact
   digests. Independently review the exact report and frozen source afterward.

The published pipeline supplies these controls. They have **not** run for this
candidate. Local metadata/axiom-parser regression tests are separate controls.
Application-specific sensitivity checks can additionally mutate only a disposable
copy: remove a selected name, change an explicit image/kernel predicate, alter a
page denominator, or change a selected theorem hypothesis while preserving
parseability. Each must be rejected by the actual protected comparison against
unchanged canonical Challenge. Such follow-up runs require a bounded approved
control plan; none is represented as already executed here. No deliberately
false assertion or custom mathematical axiom is added to the proof package.

## Rendering after mechanical acceptance

Use the same source SHA, Challenge hash and exact paths as the accepted full
report. Pin `scripts/render_challenge.py` to the pipeline commit above; use
`prepare` then `execute` with bubblewrap v0.12.0. Required repository-relative
paths are:

- project: `algebraic-hodge/ddbar-pilot`
- Challenge: `algebraic-hodge/ddbar-pilot/HodgeChallenge.lean`
- Solution: `algebraic-hodge/ddbar-pilot/HodgeSolution.lean`
- Comparator: `algebraic-hodge/ddbar-pilot/comparator.json`
- Lakefile: `algebraic-hodge/ddbar-pilot/lakefile.toml`
- toolchain: `algebraic-hodge/ddbar-pilot/lean-toolchain`

The renderer uses its own exact dependency closure and reports any proof-only
exclusions. Do not alter the Challenge or its required pins merely to fit Verso.
Rendering gets a separate exact-source authorization and resource bound; do
not start it as a side effect of the full preflight approval. Retain sanitized
HTML/JSON hashes and renderer/Verso provenance. Then inspect the rendered
mathematical statements, binder visibility, signs, quotient definitions and
source links in a browser. Rendering success and visual inspection are separate
receipts. No rendering or browser inspection is claimed yet.

## Final handoff

Reconcile documentation and metadata with actual completed receipts. Any later
status-only source still requires exact-source verification. Prepare a packet
with the exact repository/source/config paths and digests, run the repository's
release-packet guard against the full canonical report, and independently
review that receipt. Local evidence or a status-only guard cannot replace it.
Repeat current duplicates/policy checks before intake. No intake action is
part of this execution plan.
