# Verification

Author verification passed with Lean `4.35.0-rc2`, compiler commit
`11acb17ec6b07a8f9e9173e6845197929540936b`, and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The complete final gate compiled Boundary, Interior and Solution freshly
from source with warnings treated as errors. It compiled a randomly renamed
Challenge against dependency paths alone, with no local proof module on
that path. Exactly eight deliberate Challenge holes were observed. Separate
imports produced byte-identical raw `Lean.Expr` types and universe lists for
all eight selected theorems, and complete identical types and values for
`IsSubcontinuum`, `IsIndecomposable` and `composant`. No expression or binder
normalization was used. The raw comparison digest is recorded in
`verification.json`, a path-free summary. Full command, path, output and resource
receipts are retained privately.

Transitive axiom audits for all selected theorems found only `propext`,
`Classical.choice` and `Quot.sound`. The three predicate values use `propext`
and `Quot.sound`. Solution and both support modules contain no proof holes,
new axioms, unsafe declarations or native-decision shortcuts. Semantic checks
confirm the literal project definitions, the empty singleton composant,
failure of density and connectedness for the empty set in a singleton, and
relative density on an actual compact connected subtype. Dependency checks
verify literal compactness, connectedness, topology, density, meagreness,
countability, second countability and the Baire property.

The definition dossier has 19 complete pinned source files and 53 indexed
declaration bodies. Its checker compares 18 supplied Mathlib source files
with the consumed dependency source. Six negative controls are rejected:
changed bytes, changed revision, a missing predicate, a header-only declaration,
an omitted `deriving` tail, and an omitted field at the end of a `where` block.
Each truncation control adjusts its excerpt hash and displayed prose. All 53
ranges include attached declaration blocks. `Filter.countableGenerate` includes
its `deriving CountableInterFilter` line. Fresh authenticated source reads matched
all four newly included upstream Git blobs and bytes. The earlier 15-file remote
check is retained as inherited evidence. The full source files, upstream
identities and licenses remain available in `definition-evidence`.

The current official v0.4 schema and pinned Palomar metadata contract accept
the metadata. The schema rejected an invalid relationship, a thin wrapper
without a substantive source, and a negative proof-admission count. The
contract check used a duplicate-rejecting JSON decoder at the PyYAML boundary
for JSON-form YAML; it does not claim to parse arbitrary YAML. The folder
policy and exact config paths were checked against PalomarSubmission commit
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. The Lean setup action's explicit
package-directory input was checked at its pinned source revision.

Local proof stages used one serial compiler in an owned Windows Job Object
limited to one CPU, 3 GiB aggregate committed memory and 30 minutes per stage.
Private receipts contain exact argv, compiler and source hashes before and
after each stage, resource observations, exit codes and owned-process cleanup.
All owned processes terminated. Failed attempts remain in private evidence.
The support sources are checked against their authenticated upstream blobs
and built from source; their previous compiled project artifacts are not used.

Dependencies came from a read-only local cache. Fresh source and complete
artifact-family byte comparisons qualify this copied cache against the prior
complete source inventory. Revision observations are inherited; no shared
Git metadata was read and no clean dependency rebuild is claimed. A search
of all 9,084 pinned Mathlib sources for `composant` and `compossant` found no
hits. This is supporting evidence, not a proof of absence or a priority claim.

The prior workspace's ordinary Lake build failed when Git could not connect
to GitHub port 443. Its receipt is retained as inherited environment evidence.
The same route was not retried here, and no global Git, security or network
setting was changed. The previous Library helper also failed at its hosted
apps network request; that route was not retried. This target still requires
a successful hosted ordinary Lake build. CI supplies that check from the
exact target directory, followed by fresh local checks. A separately pinned
Palomar full preflight workflow supplies Comparator, NanoDa and con-ron replay.

Hosted CI, hosted Comparator and independent-kernel replay, independent review,
human mathematical review and registry acceptance are not established by these
author checks. The coordinating publication lane owns those next steps.
