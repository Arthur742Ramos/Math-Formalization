# Verification stages and exact-source evidence

This package has its own Lean4.35.0-rc2 toolchain and exact Mathlib065356 lockfile.
The proof and `OPChallenge` are byte-identical. `OPSolution` imports the proof;
the two semantic entrypoints are compiled separately. Five result contracts,
the projected strategy and six fixed game declarations have transitive audits.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

The ordinary gate builds all modules with warnings as errors, checks both semantic
entrypoints and authenticates literal upstream source evidence at the exact pin.
The native Lean checker is an additional local check with its own receipt.
These checks are not the protected canonical Palomar full workflow, NanoDa,
con-ron, Challenge rendering, browser runtime inspection or editorial review.

Completed checks belong to immutable source/run/report receipts outside this frozen
source. Compare the tested package tree, metadata and Comparator digests. Later
status-only root records do not change the package and do not constitute a rerun.
A canonical full report and renderer each require exact-source evidence. A new
fresh-runner security exception requires its own specific user approval; historical
approvals for another project grant none. No local security restriction is bypassed.

Current account, permissions, duplicate/public registration and actual private
attempts must be reconciled before intake. An empty public result does not prove
there is no pending private submission. PR35's separate frozen packet and unknown
intake state are unaffected. No registry acceptance or registration is asserted.
