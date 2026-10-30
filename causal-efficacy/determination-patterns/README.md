# Determination patterns in infinite dependency models — Lean draft

This is an independently reviewable Lean development of selected results from
the substantive prior [Isabelle formalization](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/tree/544f9084c00f4373581d230610e471fe445579e5).
The two Palomar entries below select particular theorems; neither registers the
entire manuscript or every declaration in this companion development.

| Scope | Source and verified status |
| --- | --- |
| Central pattern theorem | [PALOMAR-2026-10-29-000039 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-29-000039&version=1), source `5d035afa3d50bc9a4c3058232d5b5a2c57475026`, selects `exact_pattern_from_components` via `comparator-pattern-central.json`. |
| Uniform synthesis | [PALOMAR-2026-10-30-000001 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000001&version=1), source `72f60228093835438744c37babc68d80e330f755`, selects `local_foundation_iff_all_reachable`, `forest_copy_every_context_unique`, and `some_mechanism_every_context_unique_iff_local_foundation` via `comparator-uniform.json`. This is the unrestricted one-mechanism/all-context result; it does not assert full edge relevance. |
| Broader companion | At `4ef20fcb5adcfa2d3c9f56ee4c2ab4ffbbcc4553`, an exact-source local archive passed the umbrella Lake build, `Tests.lean`, a 61-file lexical scan and a selected 176-declaration axiom audit. The selected axioms were `propext`, `Classical.choice` and `Quot.sound`. Its central Comparator and the labelled-spine, copy-majority and uniform Comparators also passed local checks. The latter checks reused their build artifacts; independent-kernel logs report in-process `Lean.Syntax` modeling, and the labelled-spine logs also report `Nat.mul` hoisting. These are source-bound local results, not registration of the other selections. |

The later source `72f60228093835438744c37babc68d80e330f755` differs from
`4ef20fcb5adcfa2d3c9f56ee4c2ab4ffbbcc4553` only in the provenance text in
`formalization.yaml`; an independent Git-tree comparison verified identical
paths, modes and blobs for the other 2,634 tracked files. Thus the 4ef proof
and configuration inputs are unchanged at 72f. The 4ef build and audit are
historical 4ef results, not a new run attributed to this documentation update.
The uniform registry entry separately identifies 72f and its own selection.

The Isabelle artifact publishes a [verification summary](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/VERIFICATION.md),
[source manifest](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/SOURCE-SHA256SUMS),
[build script](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/build.sh)
and [regression programs](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/tree/544f9084c00f4373581d230610e471fe445579e5/tests).
The summary reports that Isabelle2025-2 checked nine extension theories and
that all three Python finite-regression programs completed successfully. The
public source artifact does not contain raw build or regression logs.

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
contribution or human mathematical review is inferred. The version-6 manuscript
was compared at statement level with the 5d source; the later companion adds the
explicit unrestricted four-gate classification described in
`MANUSCRIPT-FIDELITY-5d.md`. Philosophical interpretations are outside those
Lean checks. The Isabelle–Lean semantic interpretation in `CROSS-SYSTEM.md`
is not a cross-kernel proof.

The remaining service checks are scoped to any particular additional submission:
its exact source, selected declarations and definitions, current preflight,
rendering, duplicate and editorial assessment must be checked independently.
Unselected package results are not thereby registered. The copy-majority
construction remains a supporting manuscript proposition; its standalone
editorial interest was not established. The labelled-spine candidate's status
must be reconciled before any further intake. The following descriptions state
what each configuration selects, not an assertion that every one is registered.

Draft region necessity and sufficiency configurations are explained in
`REGION-COMPARATOR.md`. A separate
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
common Lean model. Any new combined selection requires its own definition-identity
and rendering checks; the registered central entry has only its selected scope.
The original full pattern Challenge exceeded the renderer's per-file limit at
commit 8e6792d; this observation does not describe the later registered central
Challenge. The linked `RELEASE-PLAN.md` is a historical planning snapshot; its
blanket pending statements predate the registrations and checks in the table
above. Historical, sanitized local verification records are available for
[commit 8e6792d](verification-evidence/local-8e6792d/receipt.json),
[commit 225d287](verification-evidence/local-225d287/receipt.json), and
[commit 4c57653](verification-evidence/local-4c57653/receipt.json). They
describe only those exact earlier commits.

The Isabelle extension's BSD-3-Clause notice is retained in
`SOURCE-LICENSE.txt`; the bundled AFP baseline has a separate retained notice
in `AFP-SOURCE-LICENSE.txt`. `SOURCE-ATTRIBUTION.md` is retained verbatim
from the Isabelle repository and describes the baseline bundled there; this
Lean package does not bundle that baseline. Its upstream `sources/AFP-LICENSE.txt`
corresponds to `AFP-SOURCE-LICENSE.txt` in this package. See that attribution
record for source authorship and mathematical antecedents. The two registry
records and their exact selections are identified above; the source checks do not
imply human review, novelty, journal acceptance or registration of the whole paper.

[MANUSCRIPT-EXAMPLES.md](MANUSCRIPT-EXAMPLES.md) maps the explicit
observation, shared-source, source-label, and majority-input examples and
records which explanatory statements remain outside their scope.

The [statement-level manuscript fidelity review](MANUSCRIPT-FIDELITY-5d.md)
is a historical `5d` snapshot; its successor-integration and registry-pending
statements predate the checks and registrations in the table above. The four-gate
classification was added at `4ef20fcb5adcfa2d3c9f56ee4c2ab4ffbbcc4553` and is
retained at 72f; each registered entry identifies its own source and selections.
