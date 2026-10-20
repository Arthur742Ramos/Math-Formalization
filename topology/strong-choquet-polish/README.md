# The strong Choquet characterization of Polish spaces

For every second-countable metrizable topological space, the second player has a winning full-history strong Choquet strategy if and only if the topology admits a complete metric, equivalently if and only if the space is Polish. Moves include a marked point which every response must retain. The difficult converse constructs a coherent countable response tree, proves the embedded image is Gδ, and transfers complete metrizability from the metric completion. Supporting results prove complete-metric winning strategies without second countability, complete metrizability of Gδ subsets of arbitrary complete metric spaces, actual legal-play existence and explicit empty-space behavior. This is classical mathematics; no novelty or priority is claimed.

The ten Comparator-selected declarations are:

- `StrongChoquet.exists_legalPlay`
- `StrongChoquet.strong_of_isEmpty`
- `StrongChoquet.strong_of_completeMetric`
- `StrongChoquet.strong_of_completelyMetrizable`
- `StrongChoquet.completelyMetrizable_iInter`
- `StrongChoquet.completelyMetrizable_of_isGdelta`
- `StrongChoquet.isGdelta_range_of_strong`
- `StrongChoquet.completelyMetrizable_of_strong`
- `StrongChoquet.strong_iff_completelyMetrizable`
- `StrongChoquet.polish_iff_strong`

The four exposed definitions `history`, `Follows`, `Winning` and `Strong`,
and the `Move` and `Strategy` structures, have fixed ordinary meanings.
Comparator `definition_names` is empty. A Move has a point in its open region;
each strategy reply must contain that same marked point. Strategies receive
the current move and the complete reverse list of earlier opponent moves.
Actual legal-play existence prevents hidden vacuity when an initial move exists.
The first-input and reply intersections are equal on every legal play.
An empty space has no first marked move; its explicitly constructed strategy
is winning by the empty-domain universal quantification.

For a complete metric, choose a positive-radius ball about the marked point
whose closed ball lies in the input, with radius at most2^(-history length).
Closed bounded traps shrink to a common point by completeness, and each next
trap lies inside the preceding open response. No closed ball is assumed compact.

For the converse embed into a metric ambient. At each stored original strategy
history, select a countable response cover using second countability and Lindelöf
subcovers. Nodes store exact histories, legal input refinement and the trace of
the actual strategy response. For every finite node l impose the ambient Gδ
condition V_lᶜ union the union of its children. A point satisfying all node
conditions chooses a coherent infinite legal branch. Winning supplies a common
source point, and shrinking ambient diameters identify it with the given point.
Thus the image is Gδ. This is stronger than merely intersecting level unions,
which would not ensure coherence. In the completion of a compatible metric,
the Gδ image has a complete compatible metric: a closed diagonal in a countable
product of Mathlib CompleteCopy open subsets proves that support result without
assuming second countability of the complete ambient. Homeomorphisms transport
the resulting complete metrizability back to the exact original topology.

The main theorem restricts the converse to second-countable metrizable spaces.
The general nonseparable converse, stationary strategies, quasi-Polish spaces,
open-image theorems and hyperspace results are outside scope. The complete-metric
forward result has no second-countability or nonempty premise. The image Gδ
lemma needs a second-countable metric ambient but no ambient completeness.
An arbitrary original metric need not become complete.

The classical criterion is recalled in Zsilinszky Section2 and Brian Lemma3.5,
printedp11. Dorais–Mummert printedpp2–3 supplies the marked-point/full-history
game convention; Chen Theorem11.7, printedpp18–19, inspires the countable
response-cover subtree. We prove the metric node-implication and completion
finish here. The original Choquet1969 book was not consulted.
No novelty, priority or first formalization is claimed. The research audience
includes general topology and descriptive set theory: this supplies a formal
interface between topological games and compatible complete metrics, with
applications motivating the cited work on domain representations and hyperspace
completeness. It does not formalize those papers’ new research results.

The complete-metric shrinking-trap proof and full-history convention adapt the
Apache-2.0 prior Choquet source51def6feb5e4469cce2396dfa4c9fa4f3b933d82.
All proof dependencies here are local or canonical Mathlib; Challenge imports
no other project-specific module. Prior weak Choquet Baire-product and category
target-game packages do not prove this marked-point complete-metrizability converse.

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
The established campaign-authorized roles are separate. OpenAI Codex authored
substantive proofs, tests and packaging. Reviews are independent internal AI
reviews; no human or external peer review is claimed. License: Apache-2.0.
Classification: math.GN; MSC2020 54E50,54E52,91A44.

This package owns Lean v4.35.0-rc2 and the exact nine locked Git dependencies,
including Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55. Run `lake build`
inside this directory through `/workspace/palomar-tools/run` in the prepared cloud
environment. [Material imported meanings](MATERIAL-DEFINITIONS.md) retain exact
literal definitions, attribution, dependency expansion and semantic bridges.
[Lean core evidence](CORE-DEFINITIONS.md) retains exact List/length definitions.
Both test entrypoints separately check contracts and semantics, including a
legal strategy on discrete naturals with a genuinely losing nested-tail play.
See [verification scope](VERIFICATION.md) and [review scope](REVIEW.md).
Every completed build, axiom audit, protected full check, rendering and final
review needs its own immutable external exact-source receipt. Hash consistency
does not establish semantic completeness or editorial approval. Current private
attempts and public registration remain unconfirmed; this task prepares the
manual packet and performs no registry intake.
