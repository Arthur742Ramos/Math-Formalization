# Lavrentieff exact-source checkpoint

Source: [`e2d111be48a52d4e3dd803b7b77a72b31cd59ca7`](https://github.com/Arthur742Ramos/Math-Formalization/tree/e2d111be48a52d4e3dd803b7b77a72b31cd59ca7/topology/lavrentieff-extension)
Package tree: `7b387d9479cd6b5bf8427e8f085f46c64a776f11`.
Lean4.35.0-rc2; Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.

The full theorem, supporting proofs and separate contracts are public in the
independent package. No prior package, pin, proof or registered source is changed.
Eight selected contracts have zero holes, zero definition holes and only the
standard propext, Quot.sound and Classical.choice axioms.

[Exact native receipt](exact-native-receipt.json) binds source, package tree,
metadata/configuration/pins and the original [native summary](native/summary.json).
Positive comparison and axiom audit pass; both changed-domain definition controls
compile and are rejected for the intended constant mismatch. Lean's kernel, NanoDa
and verified con-ron replay the export. NanoDa reports no typechecker errors and one
nonfatal pretty-printer diagnostic, retained in its original log; this is not hidden
or presented as a typechecker failure. Ordinary six-module build and both semantic
entrypoints pass. Exact Git-source provenance covers26 meanings25 files57 excerpts.
Metadata passes the saved v0.4 schema. [Independent review](independent-package-review.md)
and [supplemental harness review](independent-verifier-correction-review.md) identify
their exact reviewed bytes and distinguish AI review from machine/human review.

The first native attempt at predecessor e3b172c passed compilation and positive
comparison but failed negative-variant elaboration before rejection testing. Its
[original failure receipt](initial-native-attempt/receipt.json) is preserved.
The correction affects only the control's proof simplification, not theorem statements,
proofs, metadata, pins or selected definitions. The final full native procedure ran
afresh at e2d111b. No predecessor pass is attributed to changed bytes.

Canonical full verification and Challenge rendering have not been launched. The
cloud's read-only bwrap probe fails with uid-map read-only-filesystem error.
The pinned hosted install_bwrap.sh can load a new AppArmor profile through sudo;
that protected installer was not run under the user's explicit restriction.
No security settings, credentials or legal agreements were changed. No registry
intake or merge was attempted. Native receipts do not substitute for canonical
sandbox/resource-profile verification. Merge and verified intake handoff remain
blocked pending those gates, required authorization and final exact-packet review.

The public registry query receipts are retained under public-registry. Their bounded
revision509 search supports selection without promising global priority or absence
of private attempts. Hodge PR40 and sparse-equilibrium PR42 remain untouched.
The existing arthurpalomar742 repository permission was confirmed as Write; no
invitation or person-directed message was needed.
