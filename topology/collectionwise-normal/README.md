# Paracompact expansion and collectionwise separation

A classical family-expansion theorem and its collectionwise-normality consequence,
with arbitrary index cardinality. The ambient type and index type may be empty and
live in different universes.

- `Collectionwise.exists_open_expansion`: every locally finite family of arbitrary
  subsets of a paracompact space has a locally finite open expansion, indexed by
  the same type. No closedness, T1, normality or Hausdorffness is assumed.
- `Collectionwise.exists_subordinate_expansion`: for closed members in a normal
  paracompact space, the closures of the expansion can be placed inside prescribed
  open neighborhoods. No T1 assumption is needed.
- `Collectionwise.discrete_closed_iff`: a closed indexed family is discrete exactly
  when it is locally finite and pairwise disjoint.
- `Collectionwise.exists_discrete_expansion`: a discrete closed family in a normal
  paracompact space has a discrete locally finite open expansion with pairwise
  disjoint closures inside the prescribed opens.
- `Collectionwise.paracompact_hausdorff_collectionwise`: the classical Hausdorff
  application, using Mathlib’s existing paracompact normality theorem.

`IsDiscreteFamily F` means every point has a neighborhood meeting at most one
indexed member. This counts indices: repeating a nonempty member at distinct
indices is not discrete; arbitrarily many empty members are permitted.
`HasOpenExpansion F` states the literal open/locally-finite/same-index extension
contract. Both definitions are exposed and selected in Comparator.

The core proof takes a locally finite refinement of neighborhoods which meet
finitely many original members, then forms the star of each original member.
The finite-incidence argument proves local finiteness of these stars. Separation
requires two normal shrinkings and exclusion of locally finite unions of other
closures; it does not infer disjoint closures from disjoint open sets.

## Source fidelity and audience

Krajewski, *On expanding locally finite collections*, Canadian Journal of
Mathematics 23 (1971), 58–68, Theorem 2.4 and Corollary 2.4.1, is the directly
consulted source for expansion. The normal-expandable implication on p.58 supports
the application. The prescribed-open and disjoint-closure output is an explicitly
derived strengthening, not a quotation of that exact source statement.
Gutev and Loufouma Makala, arXiv:0811.3945v2 p.1, supplies definition and research
context in selection/extension theory; its selection theorems are not formalized.
Exact links and consultation limits are in `formalization.yaml`.

Mathlib already supplies locally finite refinements, normality and normal
shrinking. The earlier `perfect-paracompact` project contains an open expansion
of a particular cover inside a different proof. We credit that related work;
the arbitrary-family expansion and indexed closure-separation theorems here are
not restatements of its exported result. No new mathematics or priority is claimed.
No converse, normal-Moore theorem, selection theorem, arbitrary subspace result,
or full cardinal-restricted expansion theory is asserted.

## Attribution and verification

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These established roles are retained under the user’s explicit next-target
campaign instruction. OpenAI Codex authored substantive proofs, tests and
packaging. Separate internal AI reviewers checked the recorded scopes; no human
or external peer review is claimed. License: Apache-2.0.

`CollectionwiseChallenge.lean` contains full proofs and canonical Mathlib imports
only, byte-identical to the proof module. `CollectionwiseSolution.lean` imports
the proof module. Separate test modules check both surfaces without importing
both duplicate declaration sets. All seven selected declarations have transitive
axiom reports; only `propext`, `Classical.choice`, `Quot.sound` are permitted.

Use this package’s own `lean-toolchain`, `lake-manifest.json` and `lakefile.toml`.
In the prepared cloud environment use `/workspace/palomar-tools/run lake build`,
then `/workspace/palomar-tools/run lake env lean AxiomAudit.lean` and
`python3 scripts/check_package.py --axiom-log <fresh-log>`.
The scoped cache imports are `Mathlib.Topology.Compactness.Paracompact` only.

Ordinary Lean compilation and internal review do not establish protected
Comparator equivalence or independent-kernel acceptance. Canonical full and
Challenge-rendering checks remain unperformed for this new package. No submission
or registration is claimed. Later exact-source receipts belong in the separate
submission packet; dated evidence must not be read as a result for an edited tree.
