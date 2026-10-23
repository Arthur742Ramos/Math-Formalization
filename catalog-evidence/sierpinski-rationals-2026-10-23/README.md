# Sierpiński exact-source native verification

Native verification passed for frozen source `d33817461fadbe8d7498a237b0c5bc27dc044afb`, project `topology/sierpinski-rationals`, package tree `e54c3b7a138aa6386c73c23ae3b349c97351be5f`.

[exact-native-receipt.json](exact-native-receipt.json) binds the source, metadata, Comparator, lockfile, project archive and retained original reports. [native-summary.json](native-summary.json) is the original native report, SHA256 `13184b5038099840e195c69f4f1af7c6276a2738429199614a311c7896243198`. The source package remains unchanged by these external evidence files.

Completed checks include the package build, separately compiled Challenge/Solution semantic bridges, eighteen transitive axiom audits using only the three standard axioms, metadata schema validation, and pinned-source authentication for 41 material declarations, 35 files and 72 excerpts. Protected native comparison accepted all six contracts and all 26 primitive targets. Two independently compiled fixtures changing fixed clopen-basis/address definitions were correctly rejected. Lean's kernel, NanoDa and verified con-ron accepted the solution export; con-ron accepted 18,207 declarations. NanoDa reported 19,496 declarations without typechecking errors and one nonblocking pretty-printer message, preserved in the log.

[native-exact-evidence-review.md](native-exact-evidence-review.md) and [native-exact-review-receipt.json](native-exact-review-receipt.json) record independent internal AI authentication of all 41 native artifact hashes and all 24 frozen package files, source bindings, negative controls and kernel outcomes. Separate source, semantic and metadata review records are retained here. No human or external peer review is claimed.

The earlier [native-checkpoint.json](native-checkpoint.json) is a historical observation recorded while exact replay completion was unconfirmed. This completed exact-source receipt supersedes that pending checkpoint; it does not retroactively change the earlier observation.

To reproduce the native procedure, use the committed toolchain and manifest, run `lake build`, then `python3 scripts/verify_native.py --output-dir <external-evidence-directory>` from the package with Lean on PATH. Retain build/axiom/source-origin logs and the generated report separately from the frozen source. The project-only tar hash is identified explicitly; it is not a full registry submission archive.

Native checks do not reproduce Palomar's canonical sandbox/resource profile. Exactly one canonical full/render pair at this frozen source remains pending specific approval. [proposed-canonical/approval-request.json](proposed-canonical/approval-request.json) binds the prepared caller drafts, pinned pipeline and conditional path-specific AppArmor setup on fresh disposable restricted Ubuntu runners. The drafts are stored here, outside the active workflows directory; neither was installed or dispatched.

No canonical workflow, registry intake, registration or merge has been performed. The canonical full report, renderer result and full release-packet guard are separate gates. This is not a verified registry intake handoff.
