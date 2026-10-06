# Verification

Author checks pass with Lean `4.35.0-rc2`, compiler commit
`11acb17ec6b07a8f9e9173e6845197929540936b`, and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The verification sequence freshly compiles Boundary, Interior, Foundations, Alexandroff
and Solution with warnings treated as errors. A randomly renamed Challenge
is compiled using dependency paths alone, with no proof module available.
Exactly nine intended Challenge holes are observed. Separate imports yield
byte-identical raw Lean expression types and universe lists for all nine
selected results, and complete identical types and values for all seven
project predicates. No expression or binder normalization is applied. Only
the final dependency audit was repeated after correcting an unused-binder
warning; the proof and Challenge source hashes remained unchanged.

The transitive axiom audit permits only `propext`, `Classical.choice` and
`Quot.sound`. Proof modules have no holes, new axioms, unsafe declarations
or native-decision shortcuts. Semantic checks cover the literal project
predicates, the empty singleton composant, relative density on an induced
continuum subtype, failure of an empty open cover, vacuity of the massive
disjoint-set hypotheses on a singleton, and the impossibility of an empty
partition mapping onto a continuum. Dependency checks include continuity,
surjectivity, nonemptiness, metric balls and the compatible metric topology.

The dossier supplies 27 complete pinned upstream files and 76 complete
indexed declaration bodies. Its checker compares 24 Mathlib files with the
consumed source and rejects ten integrity controls. These include header-only
definitions, omitted attached declaration tails, a missing metric separation
field, a missing compatible metric structure field, and a missing inverse-image
refinement body, with adjusted hashes and prose. Eight new upstream files match
authenticated source reads byte for byte at the recorded commits.

The official v0.4 metadata schema and pinned Palomar contract accept the
metadata. The schema rejects three negative controls; the source-type policy
guard rejects three forbidden spellings. The contract check uses a
duplicate-rejecting JSON decoder at the PyYAML boundary for JSON-form YAML
and makes no general YAML-parser claim. Folder and configuration policy
remain pinned to PalomarSubmission
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.

Compiler stages use one owned serial compiler in a Windows Job Object capped
at one CPU, 3 GiB aggregate committed memory and 30 minutes per stage. Private
receipts record exact argv, source and compiler hashes, exit codes, observed
resources and cleanup. The final stage leaves no owned process and its source
hashes remain unchanged within each stage. Failed and cancelled attempts remain private.

Dependencies are copied from a read-only cache. All 23,590 copied source and
artifact files pass fresh byte comparison with that cache; Mathlib sources
also match the prior complete 9,084-file source inventory. Revision evidence
is inherited. No shared Git metadata is read, and no clean dependency rebuild
is claimed. The earlier GitHub port-443 and Library-helper failures are
retained as environment limits; those failed network routes are not retried.

`verification.json` is a summary without local paths. The extension still
requires a clean ordinary Lake build on a host with permitted dependency
access, followed by hosted Comparator and independent-kernel replay and
independent review. The existing target workflows run from
`topology/composants` and provide those mechanical checks. Successful checks
on the published baseline do not establish checks on this extension.
