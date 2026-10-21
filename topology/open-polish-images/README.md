# Continuous open images of Polish spaces

A continuous open surjection from a Polish space onto a metrizable space has a
Polish codomain. More generally, continuous open surjections preserve the strong
Choquet property in arbitrary topological spaces. This is classical mathematics.

The five selected contracts in `comparator.json` are:

- `OpenPolish.imageStrategy_winning`: an explicit projected strategy is winning.
- `OpenPolish.strong_image`: general strong Choquet preservation.
- `OpenPolish.completelyMetrizable_image`: second-countable completely metrizable
  source and metrizable target imply complete metrizability of the target.
- `OpenPolish.polish_image`: Polish source and metrizable target imply Polish target.
- `OpenPolish.polish_image_of_t3`: a regular T0 (hence Hausdorff) target suffices.

Each map is explicitly continuous, open and surjective. Target second countability
is proved from the source by the image-of-a-countable-basis theorem. Completeness
means a compatible complete metric exists, not that every given metric is complete.
The core transfer has no separation, countability, metric or nonemptiness hypothesis.
No arbitrary nonseparable completely-metrizable-image theorem is claimed.

## Proof and source fidelity

`imageStrategy` reconstructs a coherent source history from oldest to newest.
When the marked target point belongs to the image of the previous source reply,
its lift is chosen in that reply and its region is intersected with that reply.
Otherwise a full-preimage fallback defines a legal reply on the arbitrary history.
Every legal target play takes the constrained branch. Winning supplies one actual
common source point, whose image belongs to all target replies. We do not equate
images of infinite intersections with intersections of images.

The game uses an actual point and an open neighborhood. Responses are open,
contain that point and lie in the input neighborhood. Four fixed full-history game
definitions and both structures are inherited unchanged; there are no definition
holes. Empty-space cases are covered without hidden `Nonempty` assumptions.

Dorais–Mummert, [Proposition3.2, printedpp15–16](https://arxiv.org/pdf/0907.4126v2),
is the primary source for the new transfer. Chen's
[Section10, printedp15](https://rynchn.github.io/math/qpol.pdf) recalls the classical
Polish consequence, citing Kechris8.19; that book was not directly consulted.
No novelty, priority, stationary/convergent strategy classification, quasi-Polish
result or compact-fiber representation is claimed. The result is useful in
Polish-space constructions, open quotient maps and descriptive set theory.

`StrongChoquetFoundation.lean` is a byte-identical Apache-2.0 copy of the attributed
[prior verified foundation](https://github.com/Arthur742Ramos/Math-Formalization/blob/f2ee17b609eec4788b85043f8ad504a63cd69d86/topology/strong-choquet-polish/StrongChoquet.lean).
The protected `OPChallenge` and proof module now inline that attributed foundation
declaration body verbatim and import only the five pinned Mathlib modules. The
retained `StrongChoquetFoundation.lean` remains byte-identical historical provenance;
it is not imported by those entrypoints. The image construction is new to this package. All imports resolve inside this
standalone package or its pinned Mathlib dependency; no sibling package is imported.

## Reproducibility and review

Lean `leanprover/lean4:v4.35.0-rc2`; Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The package has its own lockfile.
`lake build` builds proof, independent Challenge/Solution contracts, semantic
bridges and transitive axiom audit. `python3 scripts/check_package.py` checks the
frozen files and supplied logs without claiming a build or canonical verification.
[MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) and
[CORE-DEFINITIONS.md](CORE-DEFINITIONS.md) retain exact meanings and attribution.
[VERIFICATION.md](VERIFICATION.md) separates verification stages;
[REVIEW.md](REVIEW.md) records review scope. Exact-source external receipts and
root preparation records govern completed stages, rather than a moving status claim.
No editorial or registration result follows merely from these checks.

Fresh global registry queries were refused with HTTP403 during selection; no
access restriction was bypassed. No equivalent was found in the inspected local
repository, active branches/PRs or pinned Mathlib, but current global registry
nonduplication is not cleared. No registry submission is recorded for this package.

## Attribution

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz.
Material new Lean proof/test/package authorship: OpenAI Codex. Independent internal
AI review is distinct from human mathematical review and external peer review.
Inherited source authorship, classical mathematics and Apache-2.0 notices are preserved.

## Protected import closure

This packaging correction repairs the candidate-local import rejected at the canonical
Challenge stage of full run39666845881 against source
`7d0d6b456b49e373e6ac6083d3f2da54e00df1d3`. Both declaration bodies are preserved
verbatim under one module header. The original failed report remains historical evidence for that earlier source.
Each ordinary/native check, independent review and separately approved exact-source
canonical pair is established only by its own immutable external receipt.
