# Explicit manuscript examples

This module adds paper-specific consequences to the general Lean development.
The reference manuscript is version 6 (PDF SHA-256
`3d50d7a574f95620c6fabd10eb5bb158d8092ff22c4bdc76e4d172ae3ea499f5`);
the matching Isabelle source is commit
`544f9084c00f4373581d230610e471fe445579e5`. The in-Lean results below do not
import Isabelle proof objects or imply cross-kernel identity.

| Manuscript item | Explicit Lean declaration(s) | Scope |
| --- | --- | --- |
| Rootless copying and conditioning, pp. 10–11 | `rootless_copy_no_roots`, `rootless_copy_admissible`, `rootless_copy_relevant`, `rootless_fixed_iff_constants`, `rootless_observed_iff_all_on`, `rootless_observed_unique`, `rootless_unconditioned_not_unique` | Natural-number carrier, successor parent, empty context; observation filters fixed points rather than replacing an equation. |
| Shared-root AND/OR, pp. 2, 5, 12 | `figure_full_and_off`, `figure_full_and_on`, `figure_full_or_off`, `figure_full_or_on`, `figure_link_states_distinct`, `figure_full_and_off_observation_impossible` | Full labelled-node states for a single shared source, constant gate, and fixed source context. The distinctness theorem shows that each two-state classification contains two different states. |
| Pointwise mechanism order versus determinacy, p. 5 | `figure_and_pointwise_le_or`, `figure_and_off_link_determined`, `figure_or_off_link_ambiguous`, `figure_determined_not_pointwise_monotone` | Same source-off context: AND is pointwise below OR on every input region but its determined region is not contained in OR's. This does not assert that either individual update operator is nonmonotone. |
| All-active context, p. 5 | `all_roots_carrier_fixed`, `all_roots_greatest_is_carrier`, `all_roots_determined_is_least` | Arbitrary carrier and parent sets, assuming only `Mechanism`; no finite-parent, inhabited-carrier, or relevance hypothesis. |
| Constant, paired, and injective labels, pp. 7–9 | `constant_source_uniform_synthesis`, `paired_source_uniform_synthesis`, `paired_no_fixed_source_in_every_tail`, `injective_sources_quantifier_separation` | Relevant synthesis chooses one mechanism for every context; the injective-label result separately proves that each legal context admits its own mechanism while no one relevant mechanism works for all contexts. |
| Removed-portion groundedness illustrations, p. 11 | `rootless_all_on_whole_portion_unfed`, `figure_and_on_all_links_unfed`, `rootless_all_on_fixed_ungrounded`, `figure_and_on_all_on_fixed_ungrounded`, `figure_or_on_all_on_fixed_grounded` | The first two exhibit the specific infinite removed portions; the third case uses the existing grounded-fixed-point characterization. The operator is unchanged. |
| Normalized two-input gates, p. 7 | `normalized_two_input_four_cases`, `four_boolean_gates_are_normalized_and_monotone`, `four_boolean_gates_are_distinct`, `boolean_four_gates_match_predicates` | Exhaustiveness on parent-restricted inputs, validity and pairwise distinction of AND, OR and the two projections, with a Bool/Prop bridge. The separate relevant-input AND/OR classification is used by the spine theorem. |
| Majority successor sensitivity, pp. 9–10 | `majority_sensitive_at_fixed_source` | Both fixed Boolean source settings with the copy input opposite the source; the stated formal input need not be a compatible global solution. |

These declarations are package-level results, not automatically protected
Comparator targets. Other groundedness illustrations, unrestricted
observation or intervention transport, and philosophical/literature conclusions
are not claimed here as separately established results. Compare the existing
source map for the general theorems and their assumptions. A local build or
source review is not Palomar intake, canonical exact-source verification, or
human peer review.

## Stage-ω and spine graph coverage

The version-6 manuscript introduces the universal-parent operator
`A(X) = {x ∈ C | Parents(x) ⊆ X}` and observes that finite parent sets
preserve increasing countable unions and give the least point by stage ω.
`PaperStageOmega.lean` states this with finite covering lists for each
carrier vertex and arbitrary carriers; it identifies the least point with
`AccessibleRegion`. It also proves the corresponding ω result separately
for an admissible contextual `Step`, whose `U` parameter may be any region;
the manuscript's root contexts are a special case. Neither theorem asserts
finite-stage stabilization, convergence of greatest fixed points, or a
finite-parent condition on the principal realization results.

The `DepthDependency` example witnesses a node accessible at
`FoundationStep FoundationOmega` but absent from `FoundationOmega`; its
graph does not satisfy `FiniteParentCover`. This is an explicit strict post-ω
example, not a general transfinite ordinal iteration framework.

`PaperGraphExamples.lean` gives the exact two distinct parents of each
labelled link, exact roots, root distance one, acyclicity, and failure of
well-foundedness for the possible-input graph; the common source in Figure 1
has infinitely many successors. It separately defines sensitivity of a link's
successor input at a fixed source context and proves its link-only relation
well founded under cofinal forcing. That relation is not the global graph or
an unrestricted state-specific causal graph. The manuscript presents the
finite-parent observation and context-sensitive graph reading as explanatory
arguments rather than additional numbered machine-checked results.

These are package-level theorems, not direct selections in the current 19
Comparator configurations; their presence does not establish protected
comparison, render compliance or registry acceptance.
