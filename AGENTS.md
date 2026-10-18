# Repository guidance

Work in the selected independent package. Preserve unrelated projects, pinned
dependencies and concurrent work. Read more specific instructions and relevant
`.agents/skills` first. Do not impose one toolchain across this monorepo.

## Choose a defensible target

- Assess the selected results against current registry criteria before
  implementation. Establish research significance and an audience from primary
  sources and concrete uses. A missing Mathlib TODO or elementary consequence
  alone is insufficient.
- Audit overlap, including equivalent statements, at the pinned library revision.
  Credit classical results, upstream definitions and prior formalizations;
  do not promise novelty or acceptance.
- Mechanical verification does not establish research significance or
  correspondence with paper and prose. Obtain independent source-fidelity and
  research-scope review before claiming readiness; record its scope and limits.

## Audit statements and proof contracts

- Match every README and metadata mathematical claim to exact binders,
  hypotheses and definitions. Check quantifiers, universes, vacuity, empty versus
  nonempty index types, integrability, pointwise versus almost-everywhere claims,
  and assumptions supplied externally or by imports. Distinguish flat and binary
  path models; prove any required connection.
- Every Comparator-selected name must elaborate in Challenge;
  `definition_names` must name definitions. Check Challenge and Solution
  namespaces/imports separately, allowed dependency closure and definition
  values. A Solution build or matching declaration types alone is insufficient.
- Proof and library code must have no `sorry`, `admit` or custom axioms. Audit
  transitive axiom dependencies of every selected declaration against the
  project's approved standard axiom allowlist.

## Keep identity and review accounts accurate

- Authors and responsible maintainers are separate roles. Verify each role's
  explicit project-authorized membership across metadata, selected README and
  validators. Do not infer maintenance from authorship, retain stale
  single-person prose, or impose a global author set. Check file attribution
  separately.
- Preserve honest AI contribution disclosures. Names do not establish human
  proof contributions. Never invent human review; distinguish internal AI
  review, human mathematical review, external peer review and machine checks.

## Pin evidence and respect intake boundaries

- Check current supported toolchain, dependency pins, packaging/file limits,
  module requirements and schema before intake. Treat requirements as versioned;
  record classification, license, title, project paths and provenance. Do not
  reuse historical limits or quotas as current policy.
- Record the actual tested commit, Comparator config, toolchain/dependency pins,
  source hashes, logs, artifacts and results. Later edits, including metadata or
  documentation, require affected consistency checks and fresh review. Prior CI
  does not prove an altered commit passed. Identify each check's commit; establish
  reviewed/verified tree equality explicitly and distinguish it from a fresh
  post-merge run.
- Verify account, duplicates and public existing-ID status. A private pending
  submission is not a public ID. Protect private submission/review URLs like
  secrets. Exclude private reviews, personal data and internal assistant/tooling
  notes from public documentation.
- This file grants no submission, withdrawal, registration, account-switch,
  invitation, permission-change or merge authority. Follow explicit user
  permissions; never evade cooldowns or quotas by changing accounts.
- Diagnose pending states from actual source/log evidence. Distinguish inference
  from observed cause; invent no queue ETA and do not infer failure from others'
  activity. Claim registration only after confirming the public record.
- Deliver exact final fields and evidence; surface blockers promptly. Separate
  completed work, failed checks and pending authorization. Do not present partial
  work under a title promising the full result.

## Mandatory release-packet review

- Review the exact proposed submission commit's own metadata, README and linked
  verification/review documents after the latest verification results are known.
  A root catalog note or an external packet does not repair contradictory claims
  inside the submitted source. Never hand off a source that says completed
  protected Comparator, independent-kernel or rendering checks have not run.
- Record completed evidence as immutable history: exact tested source, metadata
  and Comparator digests, toolchain/lockfile, report hash, run URL, selected
  theorems and definitions, and actual outcomes. Distinguish full mechanical
  verification, rendering, browser visual inspection, internal/external review,
  editorial decisions and public registration. Unknown is not failed or absent.
- Keep historical provenance stable. Do not embed a file's own future commit or
  claim an edited commit passed a predecessor's run. A later status-only source
  still needs its own exact-source report before verified intake handoff; place
  that report outside the frozen source to avoid a status-edit/verification loop.
- Before handing off verified fields run `scripts/check_release_packet.py` with
  the exact packet and its exact-source full report. Review and preserve its
  receipt independently. Use its status-only mode during correction, but never
  present that mode as a verified handoff. Check source archive bytes, copyable
  fields and metadata digest, not just a root ledger or a matching Challenge.
- Update stale validators too: no check may require an obsolete pending phrase
  or print a completed historical gate as globally unperformed. Add semantic
  negative tests for stale source claims and wrong-source/metadata evidence.
- Audit other active prospective packets for the same defect; label stale
  sources and latest-packet pointers blocked or superseded. Preserve registered
  versions and historical archives. Do not silently repair another package's
  source, attribution, pins or registration as part of a status correction.
- Reconcile intake state by actor and observation time. A previous no-intake
  packet does not negate a later user submission, and an empty public ID does
  not prove no private attempt. Resume or explicitly replace the actual attempt
  under the supported protocol; never duplicate an uncertain old-source intake.
- Reconcile existing immutable runs before scheduling verification. Security
  approval for one disposable runner/run is not permission for a fresh run.
  These release rules grant no registry, credential, account, security-setting,
  human-contact or merge authority beyond the user's explicit instructions.

## Manual pre-submission checklist

- [ ] Source mapping, overlap, research audience and independent fidelity/scope
  review are documented.
- [ ] Prose matches declarations; selected names, definitions, import contracts,
  proof closure and all axiom dependencies are checked.
- [ ] Current policy/toolchain/schema/packaging requirements and classification,
  license, title, paths and provenance are checked.
- [ ] Each authorized role agrees across metadata/README/validators; attribution,
  AI contributions and review status are accurate.
- [ ] Final commit/config/pins/hashes/logs/artifacts identify the checks performed;
  later edits and tree comparisons are accounted for.
- [ ] Account, duplicates, public ID and action authorization are verified;
  private information is excluded and cooldowns respected.
- [ ] Exact-source README/metadata/linked status prose and release-packet guard
  agree with completed receipts; independent packet review covers the final bytes.
- [ ] Exact final fields, evidence and blockers are ready for the user; claimed
  submission/registration status matches observed state.
