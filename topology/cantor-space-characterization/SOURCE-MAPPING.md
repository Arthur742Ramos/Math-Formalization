# Mathematical sources and proof mapping

The primary source statement is Anush Tserunyan, *Introduction to descriptive
set theory*, Theorem 5.3 in Section 5.B, printed page 18:
https://www.math.mcgill.ca/atserunyan/Teaching_notes/dst_lectures.pdf
The retained October21,2026 PDF has SHA256
`523e7872328aa6136054effbcc194dbe4ff2da7f177257f5d317475540acab61`.
Its source snapshot is retained outside this package in the campaign evidence.

Michael Francis, *Two Topological Uniqueness Theorems for Spaces of Real
Numbers*, arXiv:1210.1008v1, Theorem1, is a second author exposition consulted
through public text: https://arxiv.org/abs/1210.1008 . It states the compact
metrizable totally disconnected version and gives classification applications.
This package follows Tserunyan's clopen-basis formulation. The original 1910
paper was not consulted. No claim of mathematical originality is made.

| Informal requirement | Exact formal contract |
| --- | --- |
| Cantor space | `ℕ → Bool` with its product topology; `Bool` has the discrete topology |
| Homeomorphic | `Nonempty (X ≃ₜ (ℕ → Bool))`, an actual bijection continuous in both directions |
| Nonempty | `Nonempty X`, separate from perfectness |
| Compact | `CompactSpace X`, with the retained finite-subcover bridge for `IsCompact univ` |
| Metrizable | Pinned `MetrizableSpace X`; compatible metric equivalence is distinguished from its literal uniformity-plus-T0 fields |
| Zero-dimensional | `HasClopenBasis X`, literally the basis of all clopen sets |
| No isolated points | `PerfectSpace X`, with the proved punctured-neighborhood equivalence |
| Sufficient topological core | `CompactSpace`, `T2Space`, `SecondCountableTopology`, `PerfectSpace`, `Nonempty`, and the clopen-basis predicate |

The proof route differs from a vanishing-diameter scheme. A countable clopen
basis is enumerated, and each depth decides one basis element while retaining
two nonempty disjoint covering children. A compact nested intersection hits
every binary branch; basis decisions make the address map injective. No
assumption that every immediate split halves diameter is used.

The new local work is the deciding split, full covering binary scheme,
recursive point address, its continuity, compact surjectivity, separation by
basis decisions, and the intrinsic iff. Mathlib supplies countable subbases,
compact nested intersection and the compact-to-Hausdorff inverse-continuity
theorem. Its existing Cantor embeddings and compact-image surjections do not
replace these new contracts.

The clopen-cylinder and clopen-basis pullback proofs are adapted from this
campaign's Baire-space characterization at frozen source
`b77053ba8669ad046ec3c0d54d83a79724935a9f`,
`topology/baire-space-characterization/BaireCharacterization.lean`:
https://github.com/Arthur742Ramos/Math-Formalization/blob/b77053ba8669ad046ec3c0d54d83a79724935a9f/topology/baire-space-characterization/BaireCharacterization.lean
The new scheme and address construction do not import that package.

Pinned upstream attribution and exact declaration excerpts are retained in
[MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) and its JSON manifest. In
particular, Felix Weilacher's perfect-space definitions, Sébastien Gouëzel's
finite-prefix/product topology APIs, and the respective upstream file authors
retain their original attribution and Apache2.0 license notices.

The selected scope excludes Sierpiński's rational-space characterization,
the real middle-thirds Cantor set, a general total-disconnectedness bridge,
uncountable-weight spaces, and registration or editorial claims. A serious
formalization note can document this intrinsic recognition theorem and its
full binary coding for general/descriptive set theorists; no acceptance or
exhaustive novelty assertion follows from that assessment.
