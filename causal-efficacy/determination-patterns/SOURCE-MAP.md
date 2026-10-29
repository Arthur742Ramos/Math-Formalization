# Source coverage ledger — working draft

Isabelle source: `causal-efficacy-isabelle@544f9084c00f4373581d230610e471fe445579e5`.
The Isabelle pattern file SHA-256 is `045fb8504696235decbe1140f25de2373e2920ed8e76c20254fe794d58dd5202`.
This table maps selected source declarations. The principal numbered statements
below have also been compared against Library-extracted text of the 16-page
manuscript version 6, whose Library-provided SHA-256 is
`3d50d7a574f95620c6fabd10eb5bb158d8092ff22c4bdc76e4d172ae3ea499f5`.
The materialized PDF bytes are not accessible to this execution host, so an
independent local byte-hash check and final manuscript/source review remain open.

| Source declaration(s) | Lean declaration(s) | Coverage and boundary |
| --- | --- | --- |
| Patterns: `exact_relevant_pattern_realization`, `realized_pattern_necessary` | `exact_relevant_pattern_realization`, `realized_pattern_necessary`, `pattern_witness_extrema` | Arbitrary carrier and parent sets; legal context; one relevant witness. Necessity does not require relevance. |
| Patterns: `exact_relevant_region_realization`, `exact_region_realization`, `attainable_regions_context_independent` | Same names in `Regions.lean` | Separate existential witnesses at each context. |
| Determination: the four SOME/ALL fixed-context determination equivalences | Same names in `Quantifiers.lean` | Context fixed before quantifying mechanisms; reachability and accessibility are explicit. |
| Determination: `some_mechanism_every_context_unique_iff_local_foundation` and whole-carrier fixed-context uniqueness results | Same names in `Uniform.lean` | One unrestricted admissible mechanism works for all legal contexts; its chosen parent function need not equal Isabelle's choice. |
| Contexts: both all-mechanism/all-context uniqueness iff well-foundedness | Same names in `Uniform.lean` | The literal first-member/local-foundation and restricted well-foundedness bridges are in `SourceSemantics.lean`. |
| Patterns: `shared_spine_attainable_initial_segments` | Same name in `SharedSpine.lean` | Source or full carrier/finite prefixes, including zero prefix. |
| Source sharing: `relevant_labelled_spine_synthesis_iff`, `relevant_synthesis_survives_all_hard_interventions` | Same names in `LabelledSpine.lean` | Fixed labelled spine; one relevant mechanism for all contexts; arbitrary hard interventions on original links. The Lean occurrence parity is complementary to the Isabelle witness, not definitionally identical. |
| Copy-majority: `copy_majority_all_contexts`, `original_link_interventions_unique`, `carrier_expanded_solution_bridge`, both observation-preservation claims and `copy_interventions_nonunique` | Same names in `CopyMajority.lean`, with source nonuniqueness represented by `copy_interventions_not_unique` | Includes normalized/relevant full carrier mechanism. The negative example clamps all added copies on and roots off; no arbitrary added-copy intervention guarantee is asserted. |
| Patterns: `contextual_grounded_fixed_iff_least`, `active_determinate_internal_root_path` | Same names in `Bridges.lean` and `Patterns.lean` | Grounded fixed-point theorem has established antecedents; see source attribution. |
| Revision extras: source-generated target, nonempty targets and dependent-target distinct root | Same names in `SourceInference.lean` | The source-inference declarations use `EfficacyStep`, the all-roots-on contextual operator. The least solution is required. The distinct-root result assumes a carrier parent (`Grounded` there means nonroot, not the grounded-fixed-point condition). |

`BooleanTransport.lean` independently states Boolean-valued mechanism,
relevance, roots, legality, contextual operator and powerset extrema, and
proves transport to the Prop-valued Lean model. It also transports the exact
pattern theorem, with the criterion expressed through the Prop representation.
See `CROSS-SYSTEM.md` for its limits and the Isabelle HOL type interpretation.

The source includes other antecedent and supporting results, including copying
fixed-point and single-parent examples, ancestral-cone theorems, additional
finite analyses, and source-sharing graph properties. They are not individually
claimed as Lean coverage merely because a related principal theorem is present.
A full audit of the explanatory examples and appendix against the manuscript,
Mathlib/literature overlap, research-audience review and independent final
source-fidelity review remain open.
Static internal AI reviews of the included principal families have been carried
out at recorded file hashes; they are not human peer review or kernel checks.


## Numbered manuscript claims (version-6 extracted text)

| Manuscript statement | Lean declarations and boundary |
| --- | --- |
| Theorem 2 | `exact_relevant_pattern_realization`, `realized_pattern_necessary`, `pattern_witness_extrema`; the relevance-free direction uses necessity plus the relevant witness. |
| Corollary 3 | `exact_relevant_region_realization`, `exact_region_realization`, `attainable_regions_context_independent`; context-dependent witnesses may differ. The example uses `shared_spine_attainable_initial_segments`. |
| Corollary 4 | Four fixed-context SOME/ALL target equivalences in `Quantifiers.lean`, endpoint region witnesses, and four fixed-context uniqueness corollaries in `Uniform.lean`. |
| Proposition 5 | `target_accessibility_iff_ancestor_well_founded`, `every_context_target_iff_ancestor_well_founded`, `single_parent_accessible_iff_reachable`, `single_parent_some_iff_every_context_determination`, `single_parent_step_copies`. The target is a carrier subset; empty targets are included. |
| Theorem 6 | `some_mechanism_every_context_unique_iff_local_foundation` and `local_foundation_iff_all_reachable`; the one witness is not required to retain every edge. |
| Lemma 7 and Theorem 8 | `spine_unique_iff_cofinal_forcing`, `all_contexts_unique_iff_opposite_repeats`, `relevant_labelled_spine_synthesis_iff`; the hard-link result is `relevant_synthesis_survives_all_hard_interventions`. |
| Proposition 9 | `copy_majority_admissible`, `copy_majority_relevant`, `copy_majority_all_contexts`, `original_link_interventions_unique`, `carrier_expanded_solution_bridge`, `copy_interventions_nonunique`. The failure clamps all added copies; preservation concerns original-link interventions. |
| Proposition 10 | `active_determined_region_eq_least`, `active_determinate_internal_root_path`, `unique_contextual_solution_extrema`, `active_determined_nonroot_has_distinct_root`; all apply at a fixed legal context, without an all-roots-on assumption. |
| Proposition 11 | `contextual_grounded_fixed_iff_least`; this specializes the credited general theorem. |

`LocalInputs.lean` models the paper's actual parent-subset input domain and
proves admissible total extension, relevance and operator preservation, and
restriction in the other direction. The two encodings need not be equal as
total functions outside the effective parent inputs or at roots.
