# Draft registry contract

`Challenge.lean` is a self-contained proof-bearing statement surface with only
Std imported. It contains 994 physical lines and 53,880 bytes. Its principal
theorem excludes an original sixth-column extension of each of the seventeen
literal representatives. `Solution.lean` separately imports the full modular
implementation. Neither source assumes exhaustive classification or unrestricted
order-nine nonexistence.

The Challenge was extracted from the implementation by omitting unused
declarations, removing duplicate module/import/option wrappers, merging the
seventeen repeated profile-check namespace wrappers, and retaining every
required proof and literal data table. It does not pack unrelated commands on
one line to conceal its size. `challenge-extraction.json` lists selected
declarations and input hashes. The complete modular implementation remains
available alongside it. The explicit `CoveringTransforms.difference_lt` lemma
keeps the original modular bound proof under the same name in both sources.
This prevents Lean's nested-proof cache from choosing different auxiliary
proof names when declarations are combined into the standalone Challenge;
the residue value and the `Extends` predicate are unchanged.
`PORT-MANIFEST.json` records the initial port, so its historical
`TransformSoundness.lean` hash predates this named-helper repair.

The Comparator draft selects only
`CyclicDigitTransport.no_representative_extension`. Its `definition_names` list
is empty intentionally: representative data and the mathematical extension
predicate are fixed dependencies of the theorem, not replaceable definition
holes. An exact-source protected dependency-comparison receipt is required for release.

The standalone Challenge passed ordinary Lean4.35.0-rc2 elaboration/kernel
checking with only propext, Classical.choice and Quot.sound. This is not a
protected Comparator, independent-kernel, rendering or canonical full pass.
The historical native checks are identified in the metadata and retained
source-bound receipts. The prior local capacity check was blocked; that result
remains historical evidence, not an assertion about a later permitted host.
A release or registry handoff must separately provide immutable exact-source
receipts for the full official hosted preflight, including protected comparison
and independent kernels, and for canonical rendering/visual inspection and
final package review. Record current outcomes outside the frozen source,
including the exact commit, metadata digest, pins and tool revisions. Historical
native evidence alone does not establish those gates or intake readiness.

[The formalization metadata](formalization.yaml) records the project authors as
Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz,
in that order. The responsible maintainers are the same ordered trio. These
roles do not establish particular human proof contributions or human review.
Substantial AI contributions and the limited internal AI review are disclosed
in the metadata and README; no human or external peer review is claimed.
