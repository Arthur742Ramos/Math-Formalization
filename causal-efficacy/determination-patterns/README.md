# Determination patterns in infinite dependency models — Lean draft

This is an incomplete, independently reviewable Lean development of selected
results from the [Isabelle source snapshot](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/tree/544f9084c00f4373581d230610e471fe445579e5).
It is not yet a complete manuscript formalization, a release or a Palomar entry.
The principal numbered manuscript statements have been compared with the
extracted version-6 text; the private manuscript bytes match the version-6 SHA-256. Final
release-wide paper-to-source and evidence review remain open.

The current Lean development includes exact relevant forced-on/forced-off/
ambiguous pattern realization; exact attainable determinate regions and their
context-independent existential families; fixed-context SOME/ALL determination;
one admissible mechanism for all root contexts iff local foundation; the
well-foundedness and whole-carrier uniqueness corollaries; the shared-root
spine's finite-prefix classification; and one relevant mechanism on a labelled
spine iff labels repeat in every tail. It also includes the labelled-spine hard
link-intervention result, copy/majority full-carrier uniqueness, the arbitrary
original-link intervention bridge and added-copy nonuniqueness example,
positive source inference, and the credited grounded fixed-point specialization.

The scope and exact theorem map are in `SOURCE-MAP.md`. In particular, a
context-independent family of attainable regions need not use a single witness
mechanism across contexts; the general uniform mechanism theorem does not add
edge relevance; and independent variation of all ambiguous vertices is not
claimed. The labelled-spine occurrence gate differs from the Isabelle witness
by a complement while proving the same existential property.

Arthur Freitas Ramos is the formalization author and responsible maintainer.
The earlier AFP baseline is by Arthur Freitas Ramos, David Barros Hulak and
Ruy Jose Guerra Barretto de Queiroz, as credited below.

OpenAI Codex authored substantive Lean proofs and packaging; separate internal
AI reviewers checked selected statements and source fidelity. No human proof
contribution or human mathematical review is inferred. The Lake build and
internal AI source reviews are preliminary evidence only.
The precise Isabelle–Lean semantic interpretation is described in
`CROSS-SYSTEM.md`; it is not a cross-kernel proof. Final patch/evidence review and release metadata and authorship review,
release-wide protected Comparator and definition-value checks, independent
kernel checks, canonical verification and rendering remain outstanding. Local draft Comparator checks and bundled kernel replays passed on the
source revisions identified in the historical receipts; they are not the
canonical release checks. Draft region necessity and sufficiency
configurations are explained in `REGION-COMPARATOR.md`. A separate
`comparator-source.json` selects the fixed-context agreement and positive
source-inference statements from Proposition 10. A groundedness draft
`comparator-grounded.json` selects the credited general fixed-point theorem
and its Proposition 11 specialization; its standalone editorial significance
has not been established. `comparator-gate-spine.json` selects the full
relevant labelled-spine synthesis theorem, its forcing and gate-family
characterizations, and a gate-equation intervention consequence for a gate
family satisfying the opposite-repeats condition. `comparator-copy-majority.json`
selects the expanded-system mechanism, uniqueness, observation-preservation
and original-link intervention claims, together with the all-copy-clamp
nonuniqueness example. `comparator-uniform.json` selects the unrestricted
one-mechanism-for-all-contexts theorem and its forest construction. Two
additional configurations select the fixed-context accessible/reachable bounds
and relevant endpoint attainment; together they imply the SOME/ALL target
criteria for target subsets of the carrier, whose biconditionals remain separately proved in the Lean package.
`comparator-unique-bridge.json` selects the links between whole-carrier
determination, uniqueness and restricted-relation well-foundedness. The
all-mechanism/all-context biconditionals are proved in the package but are
not directly selected in this bridge. Three additional drafts select the
ancestor-cone accessibility equivalence, the single-parent accessibility and
copying claims, and the shared-spine region classification. The two Proposition
5 target-determination equivalences at a fixed legal context and the
shared-spine attainable-region theorem are separately proved in the package;
they are not directly selected by these three configurations. The shared-spine
classification combines with the region directions after matching their shared
definitions. Three further draft configurations split pattern realization into
witness admissibility/relevance, witness extrema under admissibility, and
necessity. `exact_pattern_from_components` proves their composition in the
common Lean model; cross-configuration definition identity and each rendered
entry still require validation. Each entry has only its own selected scope.
The original full pattern Challenge exceeded the renderer's per-file limit at
commit 8e6792d; the split Challenges have not yet been rendered. These drafts
and local experiments are not release certification. `RELEASE-PLAN.md` records the
remaining release requirements. Historical, sanitized local verification
records are available for [commit 8e6792d](verification-evidence/local-8e6792d/receipt.json),
[commit 225d287](verification-evidence/local-225d287/receipt.json), and
[commit 4c57653](verification-evidence/local-4c57653/receipt.json). They
describe those exact earlier commits, not this later draft.

The Isabelle extension's BSD-3-Clause notice is retained in
`SOURCE-LICENSE.txt`; the bundled AFP baseline has a separate retained notice
in `AFP-SOURCE-LICENSE.txt`. `SOURCE-ATTRIBUTION.md` is retained verbatim
from the Isabelle repository and describes the baseline bundled there; this
Lean package does not bundle that baseline. Its upstream `sources/AFP-LICENSE.txt`
corresponds to `AFP-SOURCE-LICENSE.txt` in this package. See that attribution
record for source authorship and mathematical antecedents. No human review, novelty, journal acceptance,
or registry registration is implied by the checks described here.
