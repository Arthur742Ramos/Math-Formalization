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
- [ ] Exact final fields, evidence and blockers are ready for the user; claimed
  submission/registration status matches observed state.
