# Determination patterns in infinite dependency models — Lean draft

This is an incomplete, independently reviewable Lean development of selected
results from the [Isabelle source snapshot](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/tree/544f9084c00f4373581d230610e471fe445579e5).
It is not yet a complete manuscript formalization, a release or a Palomar entry.
The principal numbered manuscript statements have been compared with the
extracted version-6 text; independently verifying the local manuscript
bytes and completing final paper-to-source review remain open.

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

OpenAI Codex authored substantive Lean proofs and packaging; separate internal
AI reviewers checked selected statements and source fidelity. No human proof
contribution or human mathematical review is inferred. The Lake build and
internal AI source reviews are preliminary evidence only.
The precise Isabelle–Lean semantic interpretation is described in
`CROSS-SYSTEM.md`; it is not a cross-kernel proof. Local verification of the
manuscript bytes, independent final patch/evidence review, release metadata and authorship,
release-wide protected Comparator and definition-value checks, independent
kernel checks, canonical verification and rendering remain outstanding. A local
pattern-only draft Comparator run and local bundled kernel replays passed; they
are not the canonical release checks. Draft region necessity and sufficiency
configurations are explained in `REGION-COMPARATOR.md`. A separate
`comparator-source.json` selects the fixed-context agreement and positive
source-inference statements from Proposition 10. These drafts and local
experiments are not release certification. `RELEASE-PLAN.md` records the
remaining release requirements.

The Isabelle extension's BSD-3-Clause notice is retained in
`SOURCE-LICENSE.txt`; the bundled AFP baseline has a separate retained notice
in `AFP-SOURCE-LICENSE.txt`. `SOURCE-ATTRIBUTION.md` is retained verbatim
from the Isabelle repository and describes the baseline bundled there; this
Lean package does not bundle that baseline. Its upstream `sources/AFP-LICENSE.txt`
corresponds to `AFP-SOURCE-LICENSE.txt` in this package. See that attribution
record for source authorship and mathematical antecedents. No human review, novelty, journal acceptance,
or registry registration is implied by the checks described here.
