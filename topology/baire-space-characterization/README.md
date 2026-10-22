# Alexandrov–Urysohn characterization of Baire space

For any topological space X, the package proves

    Nonempty (X ≃ₜ (ℕ → ℕ)) ↔ Nonempty X ∧ PolishSpace X ∧
      HasClopenBasis X ∧ CompactInteriorEmpty X.

`HasClopenBasis` literally says the clopen sets form a topological basis.
`CompactInteriorEmpty` says every compact subset has empty interior. These
fixed helper definitions are compared unchanged; `definition_names` is empty.
The space ℕ → ℕ carries its product topology, with discrete natural factors.
A homeomorphism includes a bijection and continuity in both directions.

## Source and mathematical work

This is the classical Alexandrov–Urysohn theorem, Tserunyan's Introduction to
descriptive set theory, Theorem5.4 (printedp19). The companion construction is
Problem26 in the retained18page problem PDF; alternate cached versions number
it33. Exact PDF hashes and source-version limits are in SOURCE-MAPPING.md.
No novelty, priority, human peer review or registry acceptance is claimed.

The substantive new construction chooses a non-total-bounded scale in each
nonempty complete clopen node, takes a countable clopen cover at a smaller
scale, disjointifies it and removes empty cells. A finite survivor set would
give a prohibited finite ball cover. The resulting infinite countable type is
reindexed bijectively by ℕ. This produces fully branching nonempty disjoint
clopen children with vanishing diameter. Exact cylinder images prove openness;
disjoint children prove injectivity. The continuous open bijection supplies
the inverse continuity. Necessity follows because any compact Baire subset
has finite image under each coordinate and therefore contains no cylinder.

The limit, branch-extension and cylinder-image code is adapted from the prior
[OpenBaire source](https://github.com/Arthur742Ramos/Math-Formalization/tree/87652c909a92afded15aad86a901d8c11dd75ed8/topology/open-baire-representation).
Felix Weilacher's Mathlib CantorScheme limits and generic continuity/injectivity
are reused with attribution. Open representation alone permits repetitions
and noninjective limits, so it does not give this characterization.

## Selected contracts

- `BaireCharacterization.exists_clopen_partition`
- `BaireCharacterization.exists_clopen_scheme`
- `BaireCharacterization.ClopenScheme.image_cylinder`
- `BaireCharacterization.nonempty_homeomorph_of_completeSpace`
- `BaireCharacterization.nonempty_homeomorph`
- `BaireCharacterization.baire_hasClopenBasis`
- `BaireCharacterization.baire_compactInteriorEmpty`
- `BaireCharacterization.nonempty_homeomorph_iff`

## Audience and boundaries

The theorem identifies the universal countable sequence space intrinsically;
its clopen-tree coding is used in descriptive set theory and classification
arguments on zero-dimensional Polish spaces. This is a substantive classical
formalization, not a claimed new classification theorem. Independent exact-pin
and campaign audits found no equivalent among27 prior packages or pinned
Mathlib. Public repository registrations and bounded registry searches were
checked; private/global overlap is not exhaustive. The similarly named older
`alexandroff-urysohn` project proves cover metrization, a different theorem.

Nonemptiness cannot be dropped. `TotallyDisconnectedSpace` is not substituted
for a clopen basis. Merely `¬ LocallyCompactSpace X` does not exclude a compact
open part and is not the condition formalized. No dense Gδ, irrational-space,
nonseparable or quasi-Polish extension is selected.

## Attribution and process

Authors: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz.

Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz.

OpenAI Codex provided substantive proof, testing and packaging work. Reviews
are independent internal AI reviews, separately documented; no human proof
contribution or human/external review is inferred from the names.

## Reproducibility

Lean4.35.0-rc2 and all9dependency revisions are pinned. Run `lake build` with
the committed manifest in a suitably provisioned environment. The scripts in
`scripts/` check package consistency and reproduce protected export comparison,
three altered-helper controls and native Lean/NanoDa/verified-con-ron replay.
Native results do not replace canonical full workflow or Challenge rendering.

Exact-source full/render results, wrapper commits, source archives and final
release guard receipts belong in the external immutable release packet. This
source does not assert a future workflow, editorial or registration outcome.
See VERIFICATION.md and MATERIAL-DEFINITIONS.md for the evidence boundaries.
