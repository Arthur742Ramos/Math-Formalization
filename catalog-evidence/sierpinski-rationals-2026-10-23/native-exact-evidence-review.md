# Independent exact-source native evidence review

Review date: 2026-10-23. Reviewer: independent internal OpenAI Codex AI reviewer.
Disposition: the original artifacts substantiate the claimed completed native
comparison, negative-control and independent-kernel replay results at the
frozen source identified below. No blocking native-evidence issue was found.
This is internal AI evidence review, not human or external peer review,
canonical sandbox/resource-profile verification, editorial approval or
registration.

## Frozen source and evidence identity

- Source commit: `d33817461fadbe8d7498a237b0c5bc27dc044afb`.
- Package: `topology/sierpinski-rationals`.
- Package Git tree: `e54c3b7a138aa6386c73c23ae3b349c97351be5f`.
- Original exact-run summary SHA256:
  `13184b5038099840e195c69f4f1af7c6276a2738429199614a311c7896243198`.
- Equal proof/Challenge source SHA256:
  `3a4f81807486210a423cd552b42e2614831a7ce32eb2626e90e3a1b3a2e6e459`.
- Metadata SHA256:
  `27363e33f18f1a83a059c6d8a5fb2ab3e39aac34bf3b86093b3dc4b9be126371`.
- Comparator configuration SHA256:
  `0dc2e748771265835bb67adbc0392129cd68e57adcec2aa440f9f867f5ff0510`.
- Lockfile SHA256:
  `125a575664dba67b1050f0c05c67c80490542b0b7c0b1828a4080a399341c5a2`.

The exact-run summary was independently hashed. Every one of its 41 artifact
hashes and sizes was recomputed, including both original exports, both
controlled-variant exports, the generated comparison driver, compiled driver,
protected source, fixture sources, configurations and all logs. The current
package worktree was clean. All 24 package files were compared byte-for-byte
with the frozen Git commit, and its 23-entry source manifest was checked for
complete coverage and matching digests. This binds the source, configuration,
metadata, pins and verifier script to the tested source rather than merely to
a moving branch.

The earlier preliminary summary records baseline `17efd61...` and identical
proof bytes; it was not promoted to an exact-commit result. This completed
receipt instead authenticates the original final replay naming `d338174...`.
Earlier pending observations remain historical rather than being rewritten.

## Mechanism review

The portable `scripts/verify_native.py` was read in the frozen source. It
compiles a fresh module-name copy of the Challenge outside the source package.
The copied source was independently checked equal to the frozen Challenge and
proof. Candidate and protected modules are exported separately. The generated
comparison driver imports only the installed toolchain's Lake.Check machinery,
parses the exports, and calls unmodified `Lake.Check.compareAt` and
`Lake.Check.checkAxioms` with the actual six selected targets and no definition
holes. The standard axiom list is exactly propext, Quot.sound and
Classical.choice.

The script obtains all 26 primitive constants from the selected compiler's
own `Lake/CLI/Check.lean`. The independently parsed list agrees exactly with
the final summary and driver. The Quot builtin export targets are also
included. The driver invocation matches the installed CLI's comparison and
axiom-check API sequence; it does not replace that engine with a local
signature-only approximation. Candidate code is not imported into the
comparison driver: only its export is parsed by that driver.

This is a protected-copy native check, with a fresh module identity and
separate export. It does not implement the canonical workflow's adversarial
OS isolation, trusted preparation or resource profile. No such stronger
claim is made by the reviewed documentation.

## Outcomes and negative controls

All six selected contracts are covered in Comparator order:

- `SierpinskiRationals.countable_hasClopenBasis`.
- `SierpinskiRationals.exists_binary_scheme`.
- `SierpinskiRationals.BinaryScheme.code_has_both_bits`.
- `SierpinskiRationals.BinaryScheme.codeOrder_topology`.
- `SierpinskiRationals.nonempty_homeomorph`.
- `SierpinskiRationals.nonempty_homeomorph_iff`.

The exact-run comparison exited successfully and its original log reports
completion of protected comparison and transitive axiom checking. The exact
pre-export Lake build completed successfully; fresh axiom output covers all
six targets among eighteen substantive closures, each within the permitted
three-axiom allowlist. Package/core consistency and clean pinned Mathlib-source
authentication also passed. Their original digests are retained in the
companion receipt.

Both negative fixture sources were independently reconstructed and compared
with their retained bytes. One wraps the fixed HasClopenBasis body in id.
The other wraps BinaryScheme.code in id, with a local simp id_eq repair so
the full variant remains independently compilable. Both fixture compilations
exited zero. Both exported variants were then rejected by the same driver,
with nonzero exits and the named fixed-definition mismatch in their logs:
`SierpinskiRationals.HasClopenBasis` and
`SierpinskiRationals.BinaryScheme.code` respectively. These controls exercise
the structural fixed-definition comparison paths even for definitionally
identity wrappers. They are not a claim that finitely many controls exhaust
all possible adversarial changes.

All three solution-export replays exited zero:

- Lean's default kernel accepted the export through leanchecker
  --silent --from-export. Its silent success log is retained with the recorded
  successful process exit.
- NanoDa reported 19,496 declarations with no typechecker errors. Its log also
  reports one pretty-printer error, “Unable to print axioms.” This presentation
  message is disclosed and preserved; it is not represented as a typechecking
  failure or concealed by a claim of wholly warning-free output.
- con-ron accepted 18,207 declarations in explicit --verified mode. Its log
  discloses one in-process Lean.Syntax inductive-block model, checked by its
  fold. Counts from different checkers are retained as reported rather than
  assumed to use identical counting conventions.

Installed binary digests were independently recomputed and agree with the
final summary. In particular the con-ron binary digest
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`
also agrees with the retained exact Palomar checker-policy pin for this
Lean toolchain. The companion receipt retains all six executable digests.

## Evidence limits

No extra rebuild or kernel replay was launched by this reviewer; this review
authenticates the original source-bound run and examines its mechanism and
logs. It does not claim a fresh independent upstream authentication of every
installed compiler library. Source-semantic review and current metadata
meaning were performed separately and have their own exact-byte receipts.

The final native summary records zero canonical workflow launches and zero
registry intakes. No canonical full or renderer result, browser visual check,
editorial finding, release-packet acceptance, submission or permanent
registration is certified here. Those stages retain their separate evidence
and authorization requirements. A later public evidence-only commit is not
asserted to have passed an exact-commit run merely because it contains this
receipt; tested source identity and package-tree equality must remain explicit.
