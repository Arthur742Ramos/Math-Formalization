# Validation status

The selected declarations and their exact statements appear in
`Challenge.lean` and `comparator.json`; their implementations are
exported by `Solution.lean` from `ErdosOverlap/VerifiedBound.lean`.
The pinned environment is recorded in `lean-toolchain` and
`lake-manifest.json`.

An earlier ordinary Lean run is recorded in
`reviews/full_verification/kernel_verification.json` with SHA-256
`a67bbf17b68218b0151e8c164563bc60448e4d225f5344795f29af6f5908955d`.
Its recorded hashes identify the predecessor source, before the stronger kernel,
integral certificates and protected definition/structure checks in this version.
The corresponding axiom output is
`reviews/full_verification/AuditNumeric.log`.

The historical receipt check must run on its original source checkout. It does
not validate the stronger source. The current surface audit compares statement
definitions/signatures and checks small finite instances; it does not replace
Lean or protected Comparator verification.

```sh
python3 scripts/audit_surface.py
```

For a current native run, start with an owned clean checkout without candidate
build artifacts, the exact pinned Lean/Mathlib sources and authenticated official
dependency caches. Acquire the shared verification lock and bound resources
under the monorepo policy. The complete package commands are:

```sh
lean --version
lake --version
python3 scripts/audit_surface.py
lake --fail-fast build
lake env lean NumericChallenge.lean
lake env lean NumericSolution.lean
lake env lean AuditFixedDefinitions.lean > "$EVIDENCE_DIR/AuditFixedDefinitions.log"
lake env lean AuditNumeric.lean > "$EVIDENCE_DIR/AuditNumeric.log"
python3 scripts/check_axiom_audit.py --axiom-log "$EVIDENCE_DIR/AuditNumeric.log"
```

`EVIDENCE_DIR` must be an external owned directory. Bind each command's exit
code, times, output digest, exact commit/tree and source/toolchain digests in
the native receipt. The default build includes the independent Challenge,
Solution, SemanticChallenge and SemanticSolution entrypoints. The fresh audit
covers all eleven selected theorems, fifteen fixed model definitions and both
native physical certificate records. Its parser rejects missing/duplicate
reports and axioms outside the three-name allowlist. It does not authenticate
the log or replace a successful source-bound Lean command. The separate
`AuditFixedDefinitions` command follows actual elaborated statement types and
local definition types/values, without traversing theorem proofs. It requires
every retained fixed model definition to be reached and `definition_names` to
be empty. The Comparator therefore compares their full constant information;
listing them as definition holes would skip their values.

Run the monorepo imported-definition checker in both static and
`--dependency-root` modes on the exact package and pinned Mathlib checkout.
The canonical full verifier independently performs protected comparison,
compiler checks and mandatory Lean/NanoDa
validation, and records the pinned verified con-ron replay separately.
Use the current unmodified approved execution profile and preserve any decline,
capacity failure or control failure. Rendering and visual inspection are
separate release obligations.

In addition to the canonical verifier's controls, retain a protected comparison
control with a selected theorem `recorded : chosen = chosen` and an unselected
definition `chosen : Nat`. Matching definition values must pass; changing only
`chosen` from zero to one must be rejected as a definition mismatch. Both
theorem proofs remain valid. Keep `definition_names` empty in this control;
a compilation or runner failure is not a successful rejection.

The historical protected Comparator attempt did not reach verification because
its Linux sandbox could not create a NETLINK_ROUTE socket. Its log and receipt
are included under `reviews/full_verification`. An ordinary Lean build
does not establish Comparator or NanoDa success.

The monorepo requires local native verification, the pinned canonical
full verifier and Challenge renderer, and independent source-fidelity and
patch review before merge. Its hosted workflows are retired. See the
[monorepo validation policy](https://github.com/Arthur742Ramos/Math-Formalization/blob/main/LOCAL-VALIDATION.md)
for the required controls and evidence; a source-hash or text audit is not a
replacement for them.

There is also a packaging blocker for Palomar from the monorepo's main tree:
`formalization.yaml` declares BSD-3-Clause and this package carries that
license, while the repository-root `LICENSE` is Apache-2.0. The current
Palomar source contract requires an exact match with the single root license.
Do not relabel or relicense the package merely to pass that check. A
separately identified BSD-licensed standalone commit can retain the package
files and its license, but would need its own exact-source verification,
rendering and review. It must not be merged as a replacement for the monorepo.

The release packet supplies exact-source native and canonical reports,
independent-kernel and negative-control outcomes, renderer artifacts and visual
inspection, imported-definition evidence and independent review scope. Reports
remain outside the frozen package so recording a run does not change its source.
Compare the tested package tree with the standalone and merged package trees;
tree equality identifies carried evidence and does not constitute a fresh run.
A successful local preflight is distinct from Palomar intake, editorial
acceptance or registration.
