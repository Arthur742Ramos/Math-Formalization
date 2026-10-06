# Verification

The complete local Lean audit passed on the pinned compiler and Mathlib revision. All seven proof modules were compiled afresh with warnings treated as errors. Solution and support modules contain no proof holes, new axioms, unsafe declarations, or native decision shortcuts.

A randomly renamed Challenge was compiled with dependency-only imports, independently of the proof directory. Its one intentional theorem hole was counted. Raw Lean expression types, universe parameter lists, and both literal project definition values matched Solution byte for byte. The raw comparison SHA-256 is `50e5fbd376edd70609582ea67f975d83d0b241429d788a656175d8e2be652191`. No normalization or binder-name erasure was used.

Transitive axiom audits covered the selected theorem, both definitions, ten new helper declarations, and the reused boundary-bumping theorem. Every result uses only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. The semantic audits check ordinary connectedness, compactness, subset inclusion, the unit interval, the two project definitions, strict endpoint separation, and the singleton edge case.

The definition dossier passed: 21 complete upstream files, 56 complete indexed declarations, and 20 installed Mathlib file comparisons. Six controls were rejected, including a header-only connectedness definition and omitted metric and topology structure fields.

The metadata passed the official v0.4 JSON Schema with three rejection controls. The unmodified pinned Palomar metadata validator also passed, using a duplicate-rejecting JSON decoder solely at its PyYAML decoding boundary. This checks this JSON-form YAML input; it does not validate arbitrary YAML parsing. The nested workflow’s intake and execution-profile contract passed with request ID `orderarcs001`, profile `palomar-standard-v1`, and pipeline commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. Four malformed-input controls were rejected. A syntactically valid zero SHA was used only for local intake checks; the hosted workflow supplies its actual repository commit.

Each compiler stage ran in an owned Windows Job Object with one CPU, 3 GiB aggregate committed memory, one Lean thread, and a 30-minute stage limit. The initial phase was bounded to 90 minutes of cumulative stage time. The final fresh audit took 135.11 seconds, with peak committed memory 3004743680 bytes. All 19 stages, including failed attempts, used 998.07 seconds in total. All owned process lists were empty after cleanup. Exact commands, source hashes before and after each stage, outputs, failed attempts, and resource receipts are retained privately.

The local run used owned copies of previously qualified pinned source and artifact families. It does not claim a clean Mathlib dependency rebuild. The portable verification script has a `--lake-build` path for hosted CI.

The path-filtered ordinary-build and pinned Palomar preflight workflows are prepared. Hosted Lake, Comparator, NanoDa and con-ron checks, independent review, human mathematical review, and publication have not been completed in this lane. No public repository or registry write was made. The root index and any publication base reconciliation remain with the coordinator.

[verification-summary.json](verification-summary.json) contains the privacy-safe machine-readable summary. The definition dossier and proof-source hashes identify the audited content. The public package contains no local machine paths, copied caches, compiled proof artifacts, or external atlas source.
